#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"

typedef struct HashNode HashNode;
struct HashNode {
    char *s;
    HashNode *next;
};

static HashNode *ident_tbl[1024]; /* 16 KB; hash table */

static AgType ag_type_pool[1024]; /* 16 KB */
static int next_ag_id = 1;

static DataDef data_def_pool[1024]; /* 40 KB */
static int next_data_def_id = 1;

static Instr instr_pool[16 * 1024]; /* 16 * 48 KB */
static int next_instr_id = 1;

static Block blk_pool[2 * 1024]; /* 2 * 16 KB */
static int next_blk_id = 1;

static FuncDef func_def_pool[1024]; /* 48 KB */
static int next_func_def_id = 1;

/* djb2 hashing */
static unsigned long hash(const char *s) {
    char c;
    unsigned long hash = 5381;
    while ((c = *s++) != 0) {
        hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
    }
    return hash;
}

Ident Ident_from_str(const char *s) {
    const int entries_cnt = countof(ident_tbl);
    Ident ident = {0};
    HashNode *node = 0, **node_p = 0;

    if (s) {
        ident.slot = (hash(s) % (entries_cnt - 1)) + 1;
        node_p = &ident_tbl[ident.slot];
        node = *node_p;
        while (node && node->s && strcmp(s, node->s) != 0) {
            ident.idx++;
            node_p = &node->next;
            node = *node_p;
        }
        if (!node) {
            node = calloc(1, sizeof(*node));
            node->s = w_strdup(s);
            node->next = 0;
            *node_p = node;
        }
    }
    return ident;
}

/* returns null if input is 0 */
const char *Ident_to_str(Ident s) {
    HashNode *node;
    uint16_t rem_steps;

    node = ident_tbl[s.slot];
    rem_steps = s.idx;
    assert(node);
    while (rem_steps--) {
        node = node->next;
        assert(node);
    }
    return node->s;
}

int Ident_eq(Ident x, Ident y) { return x.slot == y.slot && x.idx == y.idx; }

int Ident_is_empty(Ident x) { return x.slot == 0 && x.idx == 0; }

int Type_is_subty(Type t) {
    switch (t.t) {
    case TP_W: case TP_L: case TP_S: case TP_D:
    case TP_B: case TP_H:
    case TP_AG:
        return 1;
    }
    return 0;
}

int Type_is_extty(Type t) {
    switch (t.t) {
    case TP_W: case TP_L: case TP_S: case TP_D:
    case TP_B: case TP_H:
        return 1;
    }
    return 0;
}

int Type_is_abity(Type t) {
    switch (t.t) {
    case TP_W: case TP_L: case TP_S: case TP_D:
    case TP_SB: case TP_UB: case TP_SH: case TP_UH:
    case TP_AG:
        return 1;
    }
    return 0;
}

uint8_t _max_u8(uint8_t x, uint8_t y) {
    if (x > y) return x;
    return y;
}

uint8_t Type_log_align(Type t) {
    AgType *ag;
    int i, j;
    uint8_t max_r = 0;
    /* 1 byte => 0; 2 bytes => 1; 4 bytes => 2; 8 bytes => 3 */
    switch (t.t) {
    case TP_B: case TP_SB: case TP_UB: return 0;
    case TP_H: case TP_SH: case TP_UH: return 1;
    case TP_W: case TP_S: return 2;
    case TP_L: case TP_D: return 3;
    case TP_AG:
        ag = &ag_type_pool[t.ag_id];
        if (ag->log_align != 0x7) {
            return ag->log_align;
        }
        if (ag->is_union) {
            for (i = 0; ag->u.ub[i] != 0; ++i)
                for (j = 0; ag->u.ub[i][j].t.t != TP_UNKNOWN; ++j)
                    max_r = _max_u8(max_r, Type_log_align(ag->u.ub[i][j].t));
            return max_r;
        }
        for (i = 0; ag->u.sb[i].t.t != TP_UNKNOWN; ++i) {
            max_r = _max_u8(max_r, Type_log_align(ag->u.sb[i].t));
        }
        return max_r;
    case TP_NONE:
        fail("TP_NONE has no align");
        return 0xFF; /* unreachable */
    }
    fail("unrecognized TYPE");
    return 0xFF; /* unreachable */
}

uint32_t Type_size(Type t) {
    AgType *ag;
    int i, j;
    uint32_t s_sz, align;
    uint32_t r = 0;
    switch (t.t) {
    case TP_B: case TP_SB: case TP_UB: return 1;
    case TP_H: case TP_SH: case TP_UH: return 2;
    case TP_W: case TP_S: return 4;
    case TP_L: case TP_D: return 8;
    case TP_AG:
        ag = &ag_type_pool[t.ag_id];
        if (ag->size != 0 || ag->is_opaque) {
            return ag->size; /* zero-sized opaque is allowed */
        } else if (ag->is_union) {
            for (i = 0; ag->u.ub[i] != 0; ++i) {
                s_sz = 0;
                for (j = 0; ag->u.ub[i][j].t.t != TP_UNKNOWN; ++j) {
                    align = 1u << Type_log_align(ag->u.ub[i][j].t);
                    if (j != 0)
                        s_sz = (s_sz + align - 1) & ~(align - 1);
                    s_sz += Type_size(ag->u.ub[i][j].t) * ag->u.ub[i][j].count;
                }
                r = r > s_sz ? r : s_sz;
            }
            return r;
        }

        for (i = 0; ag->u.sb[i].t.t != TP_UNKNOWN; ++i) {
            align = 1u << Type_log_align(ag->u.sb[i].t);
            if (i != 0)
                r = (r + align - 1) & ~(align - 1);
            r += Type_size(ag->u.sb[i].t) * ag->u.sb[i].count;
        }
        return r;
    case TP_NONE:
        fail("TP_NONE has no size");
        return 0; /* unreachable */
    }
    fail("unrecognized TYPE");
    return 0; /* unreachable */
}

Type AgType_lookup_or_fail(Ident ident) {
    int prev = next_ag_id;
    Type t = AgType_lookup_or_alloc(ident);
    check(t.ag_id != prev, "type %s not found", Ident_to_str(ident));
    return t;
}

Type AgType_lookup_or_alloc(Ident ident) {
    int i;
    Type t = {0};
    t.t = TP_AG;
    for (i = 1; i < next_ag_id; ++i) {
        if (Ident_eq(ag_type_pool[i].ident, ident)) {
            t.ag_id = i;
            return t;
        }
    }

    assert((uint64_t) next_ag_id < countof(ag_type_pool) - 1);
    ag_type_pool[next_ag_id].ident = ident;
    t.ag_id = next_ag_id++;
    return t;
}

AgType *AgType_get(Type t) {
    assert(t.t == TP_AG);
    assert(t.ag_id != 0);
    return &ag_type_pool[t.ag_id];
}

uint16_t DataDef_alloc(Ident ident) {
    int r = next_data_def_id++;
    check(DataDef_lookup(ident) == 0 && FuncDef_lookup(ident) == 0,
          "redefinition of '%s'", Ident_to_str(ident));
    assert((uint64_t) next_data_def_id < countof(data_def_pool));
    data_def_pool[r].ident = ident;
    return r;
}

uint16_t DataDef_lookup(Ident ident) {
    int i;
    for (i = 1; i < next_data_def_id; ++i) {
        if (Ident_eq(ident, data_def_pool[i].ident)) {
            return i;
        }
    }
    return 0;
}

DataDef *DataDef_get(uint16_t id) {
    if (id == 0) return 0;
    assert((int) id < next_data_def_id);
    return &data_def_pool[id];
}

uint16_t FuncDef_alloc(Ident ident) {
    int r = next_func_def_id++;
    check(DataDef_lookup(ident) == 0 && FuncDef_lookup(ident) == 0,
          "redefinition of '%s'", Ident_to_str(ident));
    assert((uint64_t) next_func_def_id < countof(func_def_pool));
    func_def_pool[r].ident = ident;
    return r;
}

uint16_t FuncDef_lookup(Ident ident) {
    int i;
    for (i = 1; i < next_func_def_id; ++i) {
        if (Ident_eq(ident, func_def_pool[i].ident)) {
            return i;
        }
    }
    return 0;
}

FuncDef *FuncDef_get(uint16_t id) {
    if (id == 0) return 0;
    assert((int) id < next_func_def_id);
    return &func_def_pool[id];
}

uint16_t Block_alloc(void) {
    assert((uint64_t) next_blk_id < countof(blk_pool));
    return next_blk_id++;
}

Block *Block_get(uint16_t id) {
    if (id == 0) return 0;
    assert((int) id < next_blk_id);
    return &blk_pool[id];
}

uint32_t Instr_alloc(void) {
    assert((uint64_t) next_instr_id < countof(instr_pool));
    return next_instr_id++;
}

Instr *Instr_get(uint32_t id) {
    if (id == 0) return 0;
    assert((int) id < next_instr_id);
    return &instr_pool[id];
}

static void dump_type(Type t) {
    switch (t.t) {
    case TP_W: printf("w"); break;
    case TP_L: printf("l"); break;
    case TP_S: printf("s"); break;
    case TP_D: printf("d"); break;
    case TP_B: printf("b"); break;
    case TP_H: printf("h"); break;
    case TP_SB: printf("sb"); break;
    case TP_SH: printf("sh"); break;
    case TP_UB: printf("ub"); break;
    case TP_UH: printf("uh"); break;
    case TP_AG:
        printf("%s", Ident_to_str(AgType_get(t)->ident));
        break;
    case TP_NONE:
        break;
    default:
        fail("unrecognized TYPE kind: %d", t.t);
    }
}

static void dump_value(Value v) {
    switch (v.t) {
#if defined(__linux__)
    case V_CI: printf("%lu", v.u.u64); break;
#else
    case V_CI: printf("%llu", v.u.u64); break;
#endif
    case V_CS: printf("s_%f", v.u.s); break;
    case V_CD: printf("d_%f", v.u.d); break;
    case V_CSYM: case V_TMP:
        /* doesn't matter which _ident we use */
        printf("%s", Ident_to_str(v.u.global_ident));
        break;
    case V_CTHS:
        printf("thread %s", Ident_to_str(v.u.thread_ident));
        break;
    default:
        fail("unrecognized Value type: %d", v.t);
    }
}

void Instr_dump(Instr p) {
    int i;
    Ident empty_ident = {0};
    static const char *s[] = {
        0,
#define I(up,low) #low,
#include "instr.inc"
#undef I
        0
    };

    switch (p.t) {
    case I_CALL:
        if (p.ret_t.t != TP_NONE) {
            printf("%s =", Ident_to_str(p.ident));
            dump_type(p.ret_t);
            printf(" ");
        }
        printf("call ");
        dump_value(p.u.call.f);
        printf("(");
        for (i = 0; p.u.call.args[i].t.t != TP_UNKNOWN; ++i) {
            if (i != 0) printf(", ");
            if (i == p.u.call.va_begin_idx) printf("..., ");
            if (p.u.call.args[i].t.t == TP_NONE) {
                check(i == 0, "only first arg may be 'env'");
                printf("env ");
            } else {
                dump_type(p.u.call.args[i].t);
                printf(" ");
            }
            dump_value(p.u.call.args[i].v);
        }
        /* called func is varargs, but no varargs are provided */
        if (p.u.call.va_begin_idx == i)
            printf("%s...", i == 0 ? "" : ", ");
        printf(")");
        break;
    case I_PHI:
        printf("%s =", Ident_to_str(p.ident));
        dump_type(p.ret_t);
        printf(" phi");
        for (i = 0; p.u.phi.args[i].v.t != V_UNKNOWN; ++i) {
            if (i != 0) {
                printf(",");
            }
            printf(" %s ", Ident_to_str(p.u.phi.args[i].ident));
            dump_value(p.u.phi.args[i].v);
        }
        break;
    case I_JMP:
        printf("jmp %s", Ident_to_str(p.u.jump.dst));
        break;
    case I_JNZ:
        printf("jnz ");
        dump_value(p.u.jump.v);
        printf(", %s, %s",
               Ident_to_str(p.u.jump.dst),
               Ident_to_str(p.u.jump.dst_else));
        break;
    case I_RET:
        printf("ret");
        if (p.u.jump.v.t != V_UNKNOWN) {
            printf(" ");
            dump_value(p.u.jump.v);
        }
        break;
    case I_HLT:
        printf("hlt");
        break;
    case I_BLIT:
        printf("blit ");
        dump_value(p.u.args[0]);
        printf(", ");
        dump_value(p.u.args[1]);
        printf(", %u", p.blit_sz);
        break;
    default:
        check(I_UNKNOWN < p.t && p.t < I_END,
              "unrecognized INSTR type: %d", p.t);
        if (!Ident_eq(p.ident, empty_ident)) {
            printf("%s =", Ident_to_str(p.ident));
            dump_type(p.ret_t);
            printf(" ");
        }
        printf("%s ", s[p.t]);
        dump_value(p.u.args[0]);
        if (p.u.args[1].t != V_UNKNOWN) {
            printf(", ");
            dump_value(p.u.args[1]);
        }
    }
}

void ir_fix_typedef_size_align(void) {
    int i;
    Type t;
    AgType *ag;

    t.t = TP_AG;
    for (i = 1; i < next_ag_id; ++i) {
        t.ag_id = i;
        ag = AgType_get(t);
        if (ag->is_opaque) continue; /* already known */
        if (ag->log_align == 0x7) {
            ag->log_align = Type_log_align(t);
        }
        ag->size = Type_size(t);
        check(ag->log_align != 0x7, "log_align=7 reserved");
        check(ag->size > 0, "type size cannot be 0");
    }
}

static void dump_sb(ArrType *sb) {
    printf("{");
    while (sb->t.t != TP_UNKNOWN) {
        printf(" ");
        dump_type(sb->t);
        printf(" %d%c", sb->count, sb[1].t.t == TP_UNKNOWN ? ' ' : ',');
        sb++;
    }
    printf("}");
}

void ir_dump_typedef(void) {
    int i;
    AgType ag;
    ArrType **ub;
    for (i = 1; i < next_ag_id; ++i) {
        ag = ag_type_pool[i];
        printf("type %s = align %d ",
               Ident_to_str(ag.ident), 1 << ag.log_align);
        if (ag.is_opaque) {
            printf("{ %d }", ag.size);
        } else if (ag.is_union) {
            ub = ag.u.ub;
            printf("{");
            while (*ub) {
                printf(" ");
                dump_sb(*ub++);
            }
            printf(" }");
        } else {
            dump_sb(ag.u.sb);
        }
        printf("\n");
    }
}

/* dump string literal. */
static void dump_str(const char *s) {
    printf("\"%s\"", s);
}

static void dump_linkage(Linkage v) {
    if (v.is_export) printf("export ");
    if (v.is_thread) printf("thread ");
    if (v.is_section) {
        printf("section ");
        dump_str(v.sec_name);
        printf(" ");
        if (v.sec_flags) {
            dump_str(v.sec_flags);
            printf(" ");
        }
    }
}

void ir_dump_datadef(uint16_t id) {
    DataDef *dd;
    DataItem *p;
    int i, j;

    while (id) {
        dd = DataDef_get(id);
        dump_linkage(dd->linkage);
        printf("data %s = ", Ident_to_str(dd->ident));
        if (dd->log_align != 0xFF) {
            printf("align %d ", 1 << dd->log_align);
        }
        printf("{");
        assert(dd->items);
        for (i = 0; !dd->items[i].is_dummy_item; ++i) {
            if (dd->items[i].is_ext_ty) {
                printf(" ");
                dump_type(dd->items[i].u.ext_ty.t);
                p = dd->items[i].u.ext_ty.items;
                assert(p);
                for (j = 0; p[j].t != DI_UNKNOWN; ++j) {
                    printf(" ");
                    if (p[j].t == DI_SYM_OFF) {
                        printf("%s", Ident_to_str(p[j].u.sym_off.ident));
                        if (p[j].u.sym_off.offset) {
                            printf(" + %d", p[j].u.sym_off.offset);
                        }
                    } else if (p[j].t == DI_STR) {
                        dump_str(p[j].u.str);
                    } else {
                        assert(p[j].t == DI_CONST);
                        dump_value(p[j].u.cst);
                    }
                }
            } else {
                printf(" z %d", dd->items[i].u.zero_size);
            }
            if (!dd->items[i+1].is_dummy_item) {
                printf(",");
            }
        }
        printf(" }\n");
        id = dd->next_id;
    }
}

static void dump_instr_single(uint32_t id) {
    Instr_dump(*Instr_get(id));
    printf("\n");
}

static void dump_block(uint16_t id) {
    Block *blk;
    uint32_t instr_id;

    while (id) {
        blk = Block_get(id);
        printf("%s\n", Ident_to_str(blk->ident));
        instr_id = blk->instr_id;
        while (instr_id) {
            printf("    ");
            dump_instr_single(instr_id);
            instr_id = Instr_get(instr_id)->next_id;
        }
        if (blk->jump_id) {
            printf("    ");
            dump_instr_single(blk->jump_id);
        }
        id = blk->next_id;
    }
}

void ir_dump_funcdef(uint16_t id) {
    int i;
    FuncDef *fd;

    while (id) {
        fd = FuncDef_get(id);
        dump_linkage(fd->linkage);
        printf("function ");
        if (fd->ret_t.t != TP_NONE) {
            dump_type(fd->ret_t);
            printf(" ");
        }
        printf("%s(", Ident_to_str(fd->ident));
        for (i = 0; fd->params[i].t.t != TP_UNKNOWN; ++i) {
            if (i != 0) {
                printf(", ");
            }
            if (fd->params[i].t.t == TP_NONE) {
                printf("env");
            } else {
                dump_type(fd->params[i].t);
            }
            printf(" %s", Ident_to_str(fd->params[i].ident));
        }
        if (fd->is_varargs) {
            if (fd->params[0].t.t != TP_UNKNOWN) {
                printf(", ");
            }
            printf("...");
        }
        printf(") {\n");
        dump_block(fd->blk_id);
        printf("}\n");
        id = fd->next_id;
    }
}

static void Ident_cleanup(void) {
    const int entries_cnt = countof(ident_tbl);
    HashNode *node, *t;
    int i;

    for (i = 1; i < entries_cnt; ++i) {
        node = ident_tbl[i];
        while (node) {
            t = node;
            node = node->next;
            free(t->s);
            free(t);
        }
    }
}

static void AgType_cleanup(void) {
    int i;
    ArrType **ub;
    for (i = 1; i < next_ag_id; ++i) {
        if (ag_type_pool[i].is_opaque) {
            continue;
        } else if (ag_type_pool[i].is_union) {
            ub = ag_type_pool[i].u.ub;
            while (*ub) {
                free(*ub++);
            }
            free(ag_type_pool[i].u.ub);
        } else {
            free(ag_type_pool[i].u.sb);
        }
    }
}

static void DataDef_cleanup(void) {
    int i, j, k;
    DataDef *dd;
    DataItem *p;
    for (i = 1; i < next_data_def_id; ++i) {
        dd = &data_def_pool[i];
        assert(dd->items);
        for (j = 0; !dd->items[j].is_dummy_item; ++j) {
            if (!dd->items[j].is_ext_ty) continue;
            p = dd->items[j].u.ext_ty.items;
            assert(p);
            for (k = 0; p[k].t != DI_UNKNOWN; ++k) {
                if (p[k].t != DI_STR) continue;
                assert(p[k].u.str);
                free(p[k].u.str);
            }
            free(p);
        }
        free(dd->items);

        if(dd->linkage.sec_name)
            free(dd->linkage.sec_name);
        if(dd->linkage.sec_flags)
            free(dd->linkage.sec_flags);
    }
}

static void Instr_cleanup(void) {
    int i;
    for (i = 1; i < next_instr_id; ++i) {
        if (instr_pool[i].t == I_CALL) {
            if (instr_pool[i].u.call.args)
                free(instr_pool[i].u.call.args);
        } else if (instr_pool[i].t == I_PHI) {
            if (instr_pool[i].u.phi.args)
                free(instr_pool[i].u.phi.args);
        }
    }
}

static void FuncDef_cleanup(void) {
    int i;
    FuncDef *p;
    for (i = 1; i < next_func_def_id; ++i) {
        p = &func_def_pool[i];
        if(p->linkage.sec_name)
            free(p->linkage.sec_name);
        if(p->linkage.sec_flags)
            free(p->linkage.sec_flags);
        if (p->params)
            free(p->params);
    }
}

void ir_cleanup(void) {
    FuncDef_cleanup();
    Instr_cleanup();
    DataDef_cleanup();
    AgType_cleanup();
    Ident_cleanup();
}
