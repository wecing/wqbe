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

/* insert dummy blocks so that phi nodes always refer to jmp labels. e.g.
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
 * it becomes a dead loop. to fix that, we rewrite the program to:
 *
 *     @start
 *     @a
 *         %v =w phi @start 1, @dephi.42 0
 *     @b
 *         jnz %v, @exit, @dephi_42
 *     @dephi.42
 *         jmp @a
 *     @exit
 *         ret 0
 *
 * and after removing phi, we would get:
 *
 *     @start
 *     @a
 *         %v =w copy 1
 *     @b
 *         jnz %v, @exit, @dephi.42
 *     @dephi.42
 *         %v =w copy 0
 *         jmp @a
 *     @exit
 *         ret 0
 */
static void fix_jnz(FuncDef *fd, Block *blk) {
    Instr *jnz = Instr_get(blk->jump_id);
    Ident *dst_list[2];
    static uint32_t num = 0;
    int i;

    assert(jnz->t == I_JNZ);

    dst_list[0] = &jnz->u.jump.dst;
    dst_list[1] = &jnz->u.jump.dst_else;

    for (i = 0; i < 2; ++i) {
        uint16_t dst_blk_id = fd->blk_id;
        Block *dst_blk;
        uint16_t new_blk_id;
        Block *new_blk;
        Instr *new_jmp;

        char buf[20];
        Ident new_blk_ident;
        uint32_t instr_id;

        /* find block `*dst_list[i]` */
        while (dst_blk_id) {
            dst_blk = Block_get(dst_blk_id);
            if (Ident_eq(dst_blk->ident, *dst_list[i]))
                break;
            dst_blk_id = dst_blk->next_id;
        }
        check(dst_blk_id != 0,
              "block %s not found", Ident_to_str(*dst_list[i]));

        /* only append block if dst block has phi */
        if (dst_blk->instr_id == 0) continue;
        if (Instr_get(dst_blk->instr_id)->t != I_PHI) continue;

        num++;
        assert(num <= 65535 && "too many fix_jnz() calls");
        snprintf(buf, sizeof(buf), "@dephi.%d", num);
        new_blk_ident = Ident_from_str(buf);

        /* update dst block phi nodes */
        instr_id = dst_blk->instr_id;
        while (instr_id) {
            int j;
            Instr *instr = Instr_get(instr_id);
            instr_id = instr->next_id;
            if (instr->t != I_PHI) break;
            for (j = 0; instr->u.phi.args[j].v.t != V_UNKNOWN; ++j) {
                if (Ident_eq(instr->u.phi.args[j].ident, blk->ident))
                    instr->u.phi.args[j].ident = new_blk_ident;
            }
        }

        /* insert block */
        new_blk_id = Block_alloc();
        new_blk = Block_get(new_blk_id);
        new_blk->ident = new_blk_ident;
        new_blk->jump_id = Instr_alloc();
        new_blk->next_id = blk->next_id;
        blk->next_id = new_blk_id;
        new_jmp = Instr_get(new_blk->jump_id);
        new_jmp->t = I_JMP;
        new_jmp->u.jump.dst = *dst_list[i];

        /* update jnz */
        *dst_list[i] = new_blk_ident;
    }
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
