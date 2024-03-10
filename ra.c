#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"
#include "x64.h"
#include "tree.h"

/* RegSet = Set<uint32_t> */
struct RegSet_node {
    RB_ENTRY(RegSet_node) entry;
    uint32_t reg;
};

static int RegSet_cmp(struct RegSet_node *left, struct RegSet_node *right) {
    if (left->reg < right->reg) return -1;
    if (left->reg > right->reg) return 1;
    return 0;
}

RB_HEAD(RegSet, RegSet_node);
RB_GENERATE_STATIC(RegSet, RegSet_node, entry, RegSet_cmp)

static int RegSet_contains(struct RegSet *set, uint32_t reg) {
    struct RegSet_node find;

    find.reg = reg;
    return RB_FIND(RegSet, set, &find) != 0;
}

static void RegSet_add(struct RegSet *set, uint32_t reg) {
    struct RegSet_node *node;

    if (RegSet_contains(set, reg)) return;
    node = calloc(1, sizeof(*node));
    node->reg = reg;
    RB_INSERT(RegSet, set, node);
}

static void RegSet_clear(struct RegSet *set) {
    struct RegSet_node *node, *next;
    RB_FOREACH_SAFE(node, RegSet, set, next) {
        RB_REMOVE(RegSet, set, node);
        free(node);
    }
}

static struct {
    struct RegSet int_vregs;
    struct RegSet sse_vregs;
} ctx;

typedef struct UseDef {
    /* ends with R_END;
       mreg id => id;
       vreg id => id+R_END */
    uint32_t def[2];
    uint32_t use[3];
} UseDef;

enum GetRegIdFlag { USE, DEF };

static uint32_t
get_reg_id(uint8_t arg_t, union AsmInstrArg arg, enum GetRegIdFlag flag) {
    switch (arg_t) {
    case AP_MREG:
        /* writing to 12(%rax) does not def %rax */
        return flag == DEF && arg.mreg.is_deref ? R_END : arg.mreg.mreg;
    case AP_VREG:
        if (arg.vreg.size == SZ_S || arg.vreg.size == SZ_D)
            RegSet_add(&ctx.sse_vregs, arg.vreg.id + R_END);
        else
            RegSet_add(&ctx.int_vregs, arg.vreg.id + R_END);
        return arg.vreg.id + R_END;
    default:
        return R_END;
    }
}

static UseDef get_use_def(AsmFunc *fn, AsmInstr *ip) {
    UseDef r = { {R_END, R_END}, {R_END, R_END, R_END} };
    switch (ip->t) {
    case A_MOV: case A_MOVQ: case A_MOVS:
    case A_MOVSB: case A_MOVSL: case A_MOVSW: case A_MOVZB: case A_MOVZW:
    case A_CVTSD2S: case A_CVTSI2SD: case A_CVTSI2SS: case A_CVTSS2S:
    case A_CVTTSD2SI: case A_CVTTSS2SI:
        r.def[0] = get_reg_id(ip->arg_t[1], ip->arg[1], DEF);
        r.use[0] = get_reg_id(ip->arg_t[0], ip->arg[0], USE);
        break;
    case A_ADD: case A_ADDS: case A_SUB: case A_SUBS:
    case A_IMUL: case A_MULS: case A_DIVS:
    case A_AND: case A_OR: case A_XOR:
    case A_SAR: case A_SHL: case A_SHR:
        r.def[0] = get_reg_id(ip->arg_t[1], ip->arg[1], DEF);
        r.use[0] = get_reg_id(ip->arg_t[0], ip->arg[0], USE);
        r.use[1] = get_reg_id(ip->arg_t[1], ip->arg[1], USE);
        if (r.use[0] == R_END) {
            r.use[0] = r.use[1];
            r.use[1] = R_END;
        }
        break;
    case A_CMP: case A_UCOMIS:
        r.use[0] = get_reg_id(ip->arg_t[0], ip->arg[0], USE);
        r.use[1] = get_reg_id(ip->arg_t[1], ip->arg[1], USE);
        if (r.use[0] == R_END) {
            r.use[0] = r.use[1];
            r.use[1] = R_END;
        }
        break;
    case A_NEG:
        r.def[0] = get_reg_id(ip->arg_t[0], ip->arg[0], DEF);
        r.use[0] = get_reg_id(ip->arg_t[0], ip->arg[0], USE);
        break;
    case A_LEA:
        /* LEA 1st operand can only be addr relative to %rbp, %rsp, or %rip */
        r.def[0] = get_reg_id(ip->arg_t[1], ip->arg[1], DEF);
        break;
    case A_PUSH:
    case A__DUMMY_USE:
        r.use[0] = get_reg_id(ip->arg_t[0], ip->arg[0], USE);
        break;
    case A_SETA: case A_SETAE: case A_SETB: case A_SETBE:
    case A_SETG: case A_SETGE: case A_SETL: case A_SETLE:
    case A_SETE: case A_SETNE: case A_SETP: case A_SETNP:
    case A_POP:
    case A__DUMMY_DEF:
        r.def[0] = get_reg_id(ip->arg_t[0], ip->arg[0], DEF);
        break;
    case A_DIV: case A_IDIV:
        r.def[0] = R_RDX;
        r.def[1] = R_RAX;
        r.use[0] = R_RDX;
        r.use[1] = R_RAX;
        r.use[2] = get_reg_id(ip->arg_t[0], ip->arg[0], USE);
        break;
    case A_CLTD: case A_CQTO:
        r.def[0] = R_RDX;
        r.def[1] = R_RAX;
        r.use[0] = R_RAX;
        break;
    case A_CALL:
        /* TODO: DEF unused regs, USE all regs, DEF ret regs */
        (void)fn;
        fail("ra.c: A_CALL not implemented");
        break;
    case A_RET:
        /* nothing to do -- we rely on dummy USE marker */
        break;
    case A_JE: case A_JL: case A_JMP: case A_JNE:
    case A_UD2: case A__AS_LOC:
        break;
    default:
        fail("unsupported asm op: %d", ip->t);
    }
    return r;
}

static AsmInstr *get_instr_by_label(AsmFunc *fn, Ident ident) {
    size_t i;
    for (i = 0; i < countof(fn->label); ++i)
        if (Ident_eq(ident, fn->label[i].ident))
            return &fn->instr[fn->label[i].offset];
    fail("label %s not found", Ident_to_str(ident));
    return 0; /* unreachable */
}

static void verify_succ_ptr(AsmFunc *fn, AsmInstr *ip) {
    size_t offset;
    if (ip == 0) return;
    offset = ip - fn->instr;
    check(0 <= offset && offset < (size_t) countof(fn->instr),
          "invalid succ pointer: out of range");
    check(ip->t != A_UNKNOWN, "invalid succ pointer: not initialized");
}

static void
get_succ(AsmFunc *fn, AsmInstr *ip, AsmInstr **out1, AsmInstr **out2) {
    switch (ip->t) {
    case A_RET: case A_UD2:
        *out1 = 0;
        *out2 = 0;
        break;
    case A_JE: case A_JL: case A_JNE:
        *out1 = ip + 1;
        *out2 = get_instr_by_label(fn, ip->arg[0].sym.ident);
        break;
    case A_JMP:
        *out1 = get_instr_by_label(fn, ip->arg[0].sym.ident);
        *out2 = 0;
        break;
    default:
        *out1 = ip + 1;
        *out2 = 0;
        break;
    }
    verify_succ_ptr(fn, *out1);
    verify_succ_ptr(fn, *out2);
}

/* AsmInstrSet = Set<AsmInstr*> */
struct AsmInstrSet_node {
    RB_ENTRY(AsmInstrSet_node) entry;
    AsmInstr *elem;
};

static int AsmInstrSet_cmp(
        struct AsmInstrSet_node *left,
        struct AsmInstrSet_node *right) {
    if (left->elem < right->elem) return -1;
    if (left->elem > right->elem) return 1;
    return 0;
}

RB_HEAD(AsmInstrSet, AsmInstrSet_node);
RB_GENERATE_STATIC(AsmInstrSet, AsmInstrSet_node, entry, AsmInstrSet_cmp)

static int AsmInstrSet_contains(struct AsmInstrSet *set, AsmInstr *elem) {
    struct AsmInstrSet_node find;

    find.elem = elem;
    return RB_FIND(AsmInstrSet, set, &find) != 0;
}

static void AsmInstrSet_add(struct AsmInstrSet *set, AsmInstr *elem) {
    struct AsmInstrSet_node *node;

    if (AsmInstrSet_contains(set, elem)) return;
    node = calloc(1, sizeof(*node));
    node->elem = elem;
    RB_INSERT(AsmInstrSet, set, node);
}

static void AsmInstrSet_clear(struct AsmInstrSet *set) {
    struct AsmInstrSet_node *node, *next;
    RB_FOREACH_SAFE(node, AsmInstrSet, set, next) {
        RB_REMOVE(AsmInstrSet, set, node);
        free(node);
    }
}

/* AsmInstrInfoMap = Map<AsmInstr*, ...> */
struct AsmInstrInfoMap_node {
    RB_ENTRY(AsmInstrInfoMap_node) entry;
    AsmInstr *key;
    struct AsmInstrSet succ; /* note: max len = 2 */
    struct AsmInstrSet pred;
    struct RegSet live;
};

static int AsmInstrInfoMap_cmp(
        struct AsmInstrInfoMap_node *left,
        struct AsmInstrInfoMap_node *right) {
    if (left->key < right->key) return -1;
    if (left->key > right->key) return 1;
    return 0;
}

RB_HEAD(AsmInstrInfoMap, AsmInstrInfoMap_node);
RB_GENERATE_STATIC(
        AsmInstrInfoMap, AsmInstrInfoMap_node, entry, AsmInstrInfoMap_cmp)

static struct AsmInstrInfoMap_node *
AsmInstrInfoMap_find_or_add(struct AsmInstrInfoMap *map, AsmInstr *key) {
    struct AsmInstrInfoMap_node find;
    struct AsmInstrInfoMap_node *node;

    find.key = key;
    node = RB_FIND(AsmInstrInfoMap, map, &find);
    if (!node) {
        node = calloc(1, sizeof(*node));
        node->key = key;
        RB_INIT(&node->succ);
        RB_INIT(&node->pred);
        RB_INIT(&node->live);
        RB_INSERT(AsmInstrInfoMap, map, node);
    }
    return node;
}

static int
AsmInstrInfoMap_is_live(
        struct AsmInstrInfoMap *map, AsmInstr *ip, uint32_t reg) {
    struct AsmInstrInfoMap_node *node = AsmInstrInfoMap_find_or_add(map, ip);
    return RegSet_contains(&node->live, reg);
}

static void
AsmInstrInfoMap_mark_live(
        struct AsmInstrInfoMap *map, AsmInstr *ip, uint32_t reg) {
    struct AsmInstrInfoMap_node *node = AsmInstrInfoMap_find_or_add(map, ip);
    RegSet_add(&node->live, reg);
}

static void AsmInstrInfoMap_clear(struct AsmInstrInfoMap *map) {
    struct AsmInstrInfoMap_node *node, *next;
    RB_FOREACH_SAFE(node, AsmInstrInfoMap, map, next) {
        AsmInstrSet_clear(&node->succ);
        AsmInstrSet_clear(&node->pred);
        RegSet_clear(&node->live);
        RB_REMOVE(AsmInstrInfoMap, map, node);
        free(node);
    }
}

/* InterGraph = Map<uint32_t, Set<uint32_t>> */
struct InterGraph_node {
    RB_ENTRY(InterGraph_node) entry;
    uint32_t key;
    struct RegSet values;
    uint32_t color; /* <= R_END: not colored or pre-colored (key is mreg) */
};

static int InterGraph_cmp(
        struct InterGraph_node *left, struct InterGraph_node *right) {
    if (left->key < right->key) return -1;
    if (left->key > right->key) return 1;
    return 0;
}

RB_HEAD(InterGraph, InterGraph_node);
RB_GENERATE_STATIC(InterGraph, InterGraph_node, entry, InterGraph_cmp)

static void InterGraph_add(
        struct InterGraph *graph, uint32_t src, uint32_t dst) {
    struct InterGraph_node find;
    struct InterGraph_node *node;
    find.key = src;
    node = RB_FIND(InterGraph, graph, &find);
    if (!node) {
        node = calloc(1, sizeof(*node));
        node->key = src;
        node->color = R_END;
        RB_INIT(&node->values);
    }
    RegSet_add(&node->values, dst);
}

static void InterGraph_clear(struct InterGraph *graph) {
    struct InterGraph_node *node, *next;
    RB_FOREACH_SAFE(node, InterGraph, graph, next) {
        RegSet_clear(&node->values);
        RB_REMOVE(InterGraph, graph, node);
        free(node);
    }
}

static void record_edge(
        struct AsmInstrInfoMap *map, AsmInstr *start, AsmInstr *end) {
    struct AsmInstrInfoMap_node *map_node;

    /* insert succ edge: start -> end */
    map_node = AsmInstrInfoMap_find_or_add(map, start);
    AsmInstrSet_add(&map_node->succ, end);

    /* insert pred edge: end -> start */
    map_node = AsmInstrInfoMap_find_or_add(map, end);
    AsmInstrSet_add(&map_node->pred, start);
}

static int has_def(AsmFunc *fn, AsmInstr *ip, uint32_t reg) {
    int i;
    UseDef use_def = get_use_def(fn, ip);
    const int DEF_CNT = (int) countof(use_def.def);
    for (i = 0; i < DEF_CNT && use_def.def[i] != R_END; ++i)
        if (use_def.def[i] == reg)
            return 1;
    return 0;
}

/* mark live by register.
 *
 * this method guarantees the existance of an l' such that:
 * - succ(ip, l')
 * - live(l', reg)
 */
static void inter_visit(
        AsmFunc *fn,
        struct AsmInstrInfoMap *map,
        AsmInstr *ip,
        uint32_t reg) {
    struct AsmInstrInfoMap_node *node;
    struct AsmInstrSet_node *pred;

    /* already live: end backtracking */
    if (AsmInstrInfoMap_is_live(map, ip, reg)) return;
    /* not live here: end backtracking */
    if (has_def(fn, ip, reg)) return;

    AsmInstrInfoMap_mark_live(map, ip, reg);

    node = AsmInstrInfoMap_find_or_add(map, ip);
    RB_FOREACH(pred, AsmInstrSet, &node->pred) {
        inter_visit(fn, map, pred->elem, reg);
    }
}

/* interference graph rules:
 *
 * - live(l, x) <= use(l, x)
 * - live(l, u) <= live(l', u), succ(l, l'), not def(l, u)
 *
 * - inter(x, u) <= def(l, x), succ(l, l'), live(l', u), x != u
 */
static struct InterGraph
build_inter_graph(AsmFunc *fn) {
    int i;
    struct AsmInstrInfoMap info_map = RB_INITIALIZER(&info_map);
    struct InterGraph inter_graph = RB_INITIALIZER(&inter_graph);

    /* populate succ and pred, plus first rule of live */
    for (i = 0; fn->instr[i].t != A_UNKNOWN; ++i) {
        AsmInstr *ip = &fn->instr[i];
        AsmInstr *s1, *s2;
        UseDef use_def;
        const int USE_CNT = (int) countof(use_def.use);
        int j;

        use_def = get_use_def(fn, ip);
        for (j = 0; j < USE_CNT && use_def.use[j] != R_END; ++j) {
            AsmInstrInfoMap_mark_live(&info_map, ip, use_def.use[j]);
        }

        get_succ(fn, ip, &s1, &s2);
        if (!s1) continue;
        record_edge(&info_map, ip, s1);
        if (!s2) continue;
        record_edge(&info_map, ip, s2);
    }

    /* second rule of live */
    for (i = 0; fn->instr[i].t != A_UNKNOWN; ++i) {
        AsmInstr *ip = &fn->instr[i];
        struct AsmInstrInfoMap_node *node;

        node = AsmInstrInfoMap_find_or_add(&info_map, ip);
        if (RB_EMPTY(&node->succ)) {
            struct AsmInstrSet_node *pred;
            struct RegSet_node *live;
            RB_FOREACH(live, RegSet, &node->live) {
                RB_FOREACH(pred, AsmInstrSet, &node->pred) {
                    inter_visit(fn, &info_map, pred->elem, live->reg);
                }
            }
        }
    }

    /* interference graph */
    {
        struct AsmInstrInfoMap_node *node;
        struct AsmInstrSet_node *succ;
        RB_FOREACH(node, AsmInstrInfoMap, &info_map) {
            UseDef use_def = get_use_def(fn, node->key);
            const int DEF_CNT = (int) countof(use_def.def);
            for (i = 0; i < DEF_CNT && use_def.def[i] != R_END; ++i) {
                uint32_t x = use_def.def[i];                  /* def(l, x) */
                RB_FOREACH(succ, AsmInstrSet, &node->succ) {  /* succ(l, l') */
                    struct AsmInstrInfoMap_node *node_succ =
                        AsmInstrInfoMap_find_or_add(&info_map, succ->elem);
                    struct RegSet_node *live;
                    RB_FOREACH(live, RegSet, &node_succ->live) {
                        uint32_t u = live->reg;               /* live(l', u) */
                        if (x != u) {                         /* x != u */
                            InterGraph_add(&inter_graph, x, u);
                            InterGraph_add(&inter_graph, u, x);
                        }
                    }
                }
            }
        }
    }

    AsmInstrInfoMap_clear(&info_map);

    return inter_graph;
}

int uint32_cmp(const void *px, const void *py) {
    uint32_t x = *(uint32_t*)px;
    uint32_t y = *(uint32_t*)py;
    if (x < y) return -1;
    if (x > y) return 1;
    return 0;
}

/* fill InterGraph_node.color and return max used color. */
uint32_t color_regs(struct InterGraph *graph) {
    struct InterGraph_node *node;
    int i, regs_cnt = 0, regs_cap = 10;
    uint32_t *regs = malloc(regs_cap * sizeof(*regs));
    uint32_t max_used_color = R_END; /* nothing except mregs */

    /* get a list of all non-pre-colored regs from InterGraph */
    RB_FOREACH(node, InterGraph, graph) {
        assert(node->key != R_END);
        if (node->key < R_END) {
            node->color = node->key;
            continue;
        }
        if (regs_cnt == regs_cap) {
            regs_cap *= 2;
            regs = realloc(regs, regs_cap * sizeof(*regs));
        }
        regs[regs_cnt++] = node->key;
    }

    /* determine traversal ordering */
    /* note: RB_FOREACH() traversal is ordered, so regs is sorted */
    /* TODO: use simplicial elimination ordering */

    /* color regs with greedy algorithm */
    for (i = 0; i < regs_cnt; ++i) {
        int j;
        static const uint32_t int_mregs[] = {
            /* keep ordered by enum value */
            R_RAX, R_RCX, R_RDX, R_RSI, R_RDI, R_R8, R_R9,
            R_END
        };
        static const uint32_t sse_mregs[] = {
            R_XMM0, R_XMM1, R_XMM2, R_XMM3, R_XMM4, R_XMM5, R_XMM6, R_XMM7,
            R_XMM8, R_XMM9, R_XMM10, R_XMM11,
            R_XMM12, R_XMM13, R_XMM14, R_XMM15,
            R_END
        };
        /* used_colors : ColorSet == Set<uint32_t> == RegSet */
        struct RegSet used_colors = RB_INITIALIZER(&used_colors);
        int allow_int_regs = !RegSet_contains(&ctx.sse_vregs, regs[i]);
        int allow_sse_regs = !RegSet_contains(&ctx.int_vregs, regs[i]);
        struct RegSet_node *rs_node;
        struct InterGraph_node find;

        find.key = regs[i];
        node = RB_FIND(InterGraph, graph, &find);
        node->color = R_END;

        /* find all colors used by interfering registers */
        RB_FOREACH(rs_node, RegSet, &node->values) {
            struct InterGraph_node *interf_node;

            find.key = rs_node->reg;
            interf_node = RB_FIND(InterGraph, graph, &find);

            if (interf_node->color != R_END)
                RegSet_add(&used_colors, interf_node->color);
        }

        /* determine color */
        if (allow_int_regs)
            for (j = 0; int_mregs[j] != R_END; ++j)
                if (!RegSet_contains(&used_colors, int_mregs[j])) {
                    node->color = int_mregs[j];
                    break;
                }
        if (allow_sse_regs && node->color == R_END)
            for (j = 0; sse_mregs[j] != R_END; ++j)
                if (!RegSet_contains(&used_colors, sse_mregs[j])) {
                    node->color = sse_mregs[j];
                    break;
                }
        if (node->color == R_END) {
            node->color = R_END + 1;
            while (RegSet_contains(&used_colors, node->color))
                node->color++;
        }

        if (node->color > max_used_color)
            max_used_color = node->color;

        RegSet_clear(&used_colors);
    }

    free(regs);

    return max_used_color;
}

AsmFunc *ra_x64(AsmFunc *in_ptr) {
    struct InterGraph inter_graph;
    uint32_t max_used_color;  /* R_END + extra_colors_used */

    memset(&ctx, 0, sizeof(ctx));
    RB_INIT(&ctx.int_vregs);
    RB_INIT(&ctx.sse_vregs);

    inter_graph = build_inter_graph(in_ptr);
    max_used_color = color_regs(&inter_graph);

    // TODO: rewrite all vreg as ALLOC/mreg
    // TODO: call ra_naive???
    (void)max_used_color;

    InterGraph_clear(&inter_graph);

    RegSet_clear(&ctx.int_vregs);
    RegSet_clear(&ctx.sse_vregs);

    return 0;
}
