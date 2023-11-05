#include <assert.h>

#include "all.h"

/* naive append implementation. */
static void blk_append(FuncDef *fd, Ident blk_ident, Instr cp) {
    uint16_t blk_id;
    Block *blk;
    uint32_t instr_id, last_instr_id;
    Instr *instr;

    blk_id = fd->blk_id;
    while (blk_id) {
        blk = Block_get(blk_id);
        if (Ident_eq(blk->ident, blk_ident))
            break;
        blk_id = blk->next_id;
    }
    check(blk_id, "block %s not found in function %s",
          Ident_to_str(blk_ident), Ident_to_str(fd->ident));

    cp.next_id = 0;
    instr_id = Instr_alloc();
    *Instr_get(instr_id) = cp;

    last_instr_id = blk->instr_id;
    while (last_instr_id) {
        instr = Instr_get(last_instr_id);
        if (instr->next_id == 0)
            break;
        last_instr_id = instr->next_id;
    }

    if (last_instr_id)
        instr->next_id = instr_id;
    else
        blk->instr_id = instr_id;
}

/* naive lookup. */
static Type type_of(FuncDef *fd, Ident ident) {
    int i;
    uint16_t blk_id;
    Block *blk;
    uint32_t instr_id;
    Instr *instr;
    Type unused = {0};

    for (i = 0; fd->params[i].t.t != TP_UNKNOWN; ++i)
        if (Ident_eq(ident, fd->params[i].ident))
            return fd->params[i].t;

    blk_id = fd->blk_id;
    while (blk_id) {
        blk = Block_get(blk_id);
        blk_id = blk->next_id;

        instr_id = blk->instr_id;
        while (instr_id) {
            instr = Instr_get(instr_id);
            instr_id = instr->next_id;

            if (instr->ret_t.t != TP_NONE &&
                instr->ret_t.t != TP_UNKNOWN &&
                Ident_eq(instr->ident, ident)) {
                return instr->ret_t;
            }
        }
    }

    fail("ident %s not found in function %s",
         Ident_to_str(ident), Ident_to_str(fd->ident));
    return unused; /* unreachable */
}

/*
 * backup jnz condition so that it would be safe to
 * insert dephi copy ops before it. e.g.
 *
 *     @start
 *     @a
 *         %v =w phi @start 1, @b 0
 *     @b
 *         jnz %v, @exit, @a
 *     @exit
 *         ret 0
 *
 * if we simply replace phi with copy ops before jump ops:
 *
 *     @start
 *         %v =w copy 1
 *     @a
 *     @b
 *         %v =w copy 0
 *         jnz %v, @exit, @a
 *     @exit
 *         ret 0
 *
 * it becomes a dead loop. to fix that, we could backup jnz condition:
 *
 *     @start
 *     @a
 *         %v =w phi @start 1, @b 0
 *     @b
 *         %_t =w copy %v
 *         jnz %_t, @exit, @a
 *     @exit
 *         ret 0
 *
 * and after removing phi, we would get:
 *
 *     @start
 *         %v =w copy 1
 *     @a
 *     @b
 *         %_t =w copy %v
 *         %v =w copy 0
 *         jnz %_t, @exit, @a
 *     @exit
 *         ret 0
 */
static void fix_jnz(FuncDef *fd, Block *blk) {
    Instr *jnz;
    Instr cp = {0};
    Type cond_tp;
    static uint32_t num = 0;
    char buf[35];

    jnz = Instr_get(blk->jump_id);
    if (jnz->u.jump.v.t != V_TMP)
        return; /* no need to fix jnz */
    cond_tp = type_of(fd, jnz->u.jump.v.u.tmp_ident);

    assert(num <= 65535 && "too many fix_jnz() calls");
    assert(jnz->t == I_JNZ);
    sprintf(buf, "%%.wqbe.dephi.fix_jnz.%u", num++);

    cp.t = I_COPY;
    cp.next_id = 0;
    cp.ret_t = cond_tp;
    cp.ident = Ident_from_str(buf);
    cp.u.args[0] = jnz->u.jump.v;
    blk_append(fd, blk->ident, cp);

    jnz->u.jump.v.u.tmp_ident = cp.ident;
}

void dephi(FuncDef *fd) {
    uint16_t blk_id;
    Block *blk;
    Instr *p;
    Instr cp = {0};
    int i;

    cp.t = I_COPY;
    cp.next_id = 0;

    blk_id = fd->blk_id;
    while (blk_id) {
        blk = Block_get(blk_id);
        blk_id = blk->next_id;
        if (Instr_get(blk->jump_id)->t == I_JNZ)
            fix_jnz(fd, blk);
    }

    blk_id = fd->blk_id;
    while (blk_id) {
        blk = Block_get(blk_id);
        blk_id = blk->next_id;

        while (blk->instr_id) {
            p = Instr_get(blk->instr_id);
            if (p->t != I_PHI)
                break;
            for (i = 0; p->u.phi.args[i].v.t != V_UNKNOWN; ++i) {
                cp.ret_t = p->ret_t;
                cp.ident = p->ident;
                cp.u.args[0] = p->u.phi.args[i].v;
                blk_append(fd, p->u.phi.args[i].ident, cp);
            }
            /* discard instr. */
            blk->instr_id = p->next_id;
        }
    }
}
