#include <assert.h>
#include <stdlib.h>

#include "all.h"

/* naive append implementation. */
static void blk_append(FuncDef *fd, Ident blk_ident, Instr cp) {
    uint16_t blk_id;
    Block *blk;
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

    instr = Instr_alloc();
    *instr = cp;

    Block_append_before_jump(blk, instr);
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
 *         %v =w phi @start 1, @dephi.blk.42 0
 *     @b
 *         jnz %v, @exit, @dephi.blk.42
 *     @dephi.blk.42
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
 *         jnz %v, @exit, @dephi.blk.42
 *     @dephi.blk.42
 *         %v =w copy 0
 *         jmp @a
 *     @exit
 *         ret 0
 */
static void fix_jnz(FuncDef *fd, Block *blk) {
    Instr *jnz = blk->dummy_tail->prev;
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

        char buf[30];
        Ident new_blk_ident;
        Instr *instr;

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
        if (dst_blk->dummy_head->next->t != I_PHI) continue;

        num++;
        assert(num <= 65535 && "too many fix_jnz() calls");
        w_snprintf(buf, sizeof(buf), "@dephi.blk.%d", num);
        new_blk_ident = Ident_from_str(buf);

        /* update dst block phi nodes */
        instr = dst_blk->dummy_head->next;
        for (; instr->t == I_PHI; instr = instr->next) {
            int j;
            for (j = 0; instr->u.phi.args[j].v.t != V_UNKNOWN; ++j) {
                if (Ident_eq(instr->u.phi.args[j].ident, blk->ident))
                    instr->u.phi.args[j].ident = new_blk_ident;
            }
        }

        /* insert block */
        new_blk_id = Block_alloc();
        new_blk = Block_get(new_blk_id);
        new_blk->ident = new_blk_ident;
        new_blk->next_id = blk->next_id;
        blk->next_id = new_blk_id;
        new_jmp = Instr_alloc();
        new_jmp->t = I_JMP;
        new_jmp->u.jump.dst = *dst_list[i];
        Block_append(new_blk, new_jmp);

        /* update jnz */
        *dst_list[i] = new_blk_ident;
    }
}

void dephi(FuncDef *fd) {
    uint16_t blk_id;
    Block *blk;
    Instr *p;
    Instr cp = {0};
    Value v = {0};
    int i, j;
    static int num = 0;
    char buf[30];

    cp.t = I_COPY;

    v.t = V_TMP;

    blk_id = fd->blk_id;
    while (blk_id) {
        blk = Block_get(blk_id);
        blk_id = blk->next_id;
        if (blk->dummy_tail->prev->t == I_JNZ)
            fix_jnz(fd, blk);
    }

    blk_id = fd->blk_id;
    while (blk_id) {
        int phi_cnt = 0;
        Ident *v_idents = 0;

        blk = Block_get(blk_id);
        blk_id = blk->next_id;

        /* from:
         *
         *     @x
         *         %a =w phi @s 380, @y %r
         *         %b =w phi @s 747, @y %a
         *         ...
         *     @y
         *         jmp @x
         *     @s
         *         jmp @x
         *
         * to:
         *
         *     @x
         *         ...
         *     @y
         *         # backup old value
         *         %dephi.1 =w copy %r
         *         %dephi.2 =w copy %a
         *         # overwrite old value
         *         %a =w copy %dephi.1
         *         %b =w copy %dephi.2
         *         jmp @x
         *     @s
         *         %dephi.1 =w copy 380
         *         %dephi.2 =w copy 747
         *         %a =w copy %dephi.1
         *         %b =w copy %dephi.2
         *         jmp @x
         */

        /* backup old value */
        for (p = blk->dummy_head->next; p->t == I_PHI; p = p->next)
            phi_cnt++;
        if (phi_cnt)
            v_idents = malloc(sizeof(Ident) * phi_cnt);
        j = 0;
        for (p = blk->dummy_head->next; p->t == I_PHI; p = p->next) {
            num++;

            /* just a random safety check */
            assert(num <= 65535 && "too many dephi() calls");

            w_snprintf(buf, sizeof(buf), "%%dephi.%d", num);
            v_idents[j] = Ident_from_str(buf);

            /* add e.g. %dephi.42 =w copy %r */
            for (i = 0; p->u.phi.args[i].v.t != V_UNKNOWN; ++i) {
                cp.ret_t = p->ret_t;
                cp.ident = v_idents[j];
                cp.u.args[0] = p->u.phi.args[i].v;
                blk_append(fd, p->u.phi.args[i].ident, cp);
            }

            j++;
        }

        /* overwrite old value, remove phi */
        j = 0;
        for (p = blk->dummy_head->next; p->t == I_PHI; p = p->next) {
            /* add e.g. %a =w copy %dephi.42 */
            for (i = 0; p->u.phi.args[i].v.t != V_UNKNOWN; ++i) {
                cp.ret_t = p->ret_t;
                cp.ident = p->ident;
                v.u.tmp_ident = v_idents[j];
                cp.u.args[0] = v;
                blk_append(fd, p->u.phi.args[i].ident, cp);
            }
            j++;
            /* do not discard p yet; we still need p->next */
        }
        /* discard instr between dummy_head and p (exclusive) */
        while (blk->dummy_head->next != p) {
            Instr *t = blk->dummy_head->next;
            t->next->prev = t->prev;
            t->prev->next = t->next;
            Instr_free(t);
        }

        if (v_idents)
            free(v_idents);
    }
}
