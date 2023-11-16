#include <assert.h>
#include <string.h>

#include "all.h"
#include "x64.h"

static const Ident empty_ident;

static const char *op_table[] = {
    0, /* A_UNKNOWN */
#define A(up,low) #low,
#include "x64.inc"
#undef A
    0 /* A_END */
};

/* in QBE, 1/2/4/8 bytes ints are named B/H/W/L,
   while X64 uses b/w/l/q (e.g. pushq). */
enum {
    X64_SZ_NONE = SZ_NONE,
    X64_SZ_B = SZ_B,
    X64_SZ_W = SZ_H,
    X64_SZ_L = SZ_W,
    X64_SZ_Q = SZ_L,
    X64_SZ_S = SZ_S,
    X64_SZ_D = SZ_D
};

static void dump_sz(uint8_t sz) {
    switch (sz) {
    case X64_SZ_NONE: return;
    case X64_SZ_B: printf("b"); return;
    case X64_SZ_W: printf("w"); return;
    case X64_SZ_L: printf("l"); return;
    case X64_SZ_Q: printf("q"); return;
    case X64_SZ_S: printf("s"); return;
    case X64_SZ_D: printf("d"); return;
    }
    fail("unrecognized instr size");
}

static void dump_mreg(uint8_t mreg, uint8_t size) {
    assert(size != X64_SZ_NONE);
    printf("%%");
    if (size == X64_SZ_Q) {
        switch (mreg) {
        case R_RAX: printf("rax"); return;
        case R_RBX: printf("rbx"); return;
        case R_RCX: printf("rcx"); return;
        case R_RDX: printf("rdx"); return;
        case R_RSI: printf("rsi"); return;
        case R_RDI: printf("rdi"); return;
        case R_RBP: printf("rbp"); return;
        case R_RSP: printf("rsp"); return;
        case R_R8:  printf("r8");  return;
        case R_R9:  printf("r9");  return;
        case R_R10: printf("r10"); return;
        case R_R11: printf("r11"); return;
        case R_R12: printf("r12"); return;
        case R_R13: printf("r13"); return;
        case R_R14: printf("r14"); return;
        case R_R15: printf("r15"); return;
        }
    } else if (size == X64_SZ_L) {
        switch (mreg) {
        case R_RAX: printf("eax"); return;
        case R_RBX: printf("ebx"); return;
        case R_RCX: printf("ecx"); return;
        case R_RDX: printf("edx"); return;
        case R_RSI: printf("esi"); return;
        case R_RDI: printf("edi"); return;
        case R_RBP: printf("ebp"); return;
        case R_RSP: printf("esp"); return;
        case R_R8:  printf("r8d"); return;
        case R_R9:  printf("r9d"); return;
        case R_R10: printf("r10d"); return;
        case R_R11: printf("r11d"); return;
        case R_R12: printf("r12d"); return;
        case R_R13: printf("r13d"); return;
        case R_R14: printf("r14d"); return;
        case R_R15: printf("r15d"); return;
        }
    } else if (size == X64_SZ_W) {
        switch (mreg) {
        case R_RAX: printf("ax"); return;
        case R_RBX: printf("bx"); return;
        case R_RCX: printf("cx"); return;
        case R_RDX: printf("dx"); return;
        case R_RSI: printf("si"); return;
        case R_RDI: printf("di"); return;
        case R_RBP: printf("bp"); return;
        case R_RSP: printf("sp"); return;
        case R_R8:  printf("r8w"); return;
        case R_R9:  printf("r9w"); return;
        case R_R10: printf("r10w"); return;
        case R_R11: printf("r11w"); return;
        case R_R12: printf("r12w"); return;
        case R_R13: printf("r13w"); return;
        case R_R14: printf("r14w"); return;
        case R_R15: printf("r15w"); return;
        }
    } else if (size == X64_SZ_B) {
        switch (mreg) {
        case R_RAX: printf("al"); return;
        case R_RBX: printf("bl"); return;
        case R_RCX: printf("cl"); return;
        case R_RDX: printf("dl"); return;
        case R_RSI: printf("sil"); return;
        case R_RDI: printf("dil"); return;
        case R_RBP: printf("bpl"); return;
        case R_RSP: printf("spl"); return;
        case R_R8:  printf("r8b"); return;
        case R_R9:  printf("r9b"); return;
        case R_R10: printf("r10b"); return;
        case R_R11: printf("r11b"); return;
        case R_R12: printf("r12b"); return;
        case R_R13: printf("r13b"); return;
        case R_R14: printf("r14b"); return;
        case R_R15: printf("r15b"); return;
        }
    } else {
        assert(size == X64_SZ_S || size == X64_SZ_D);
        switch (mreg) {
        case R_XMM0: printf("xmm0"); return;
        case R_XMM1: printf("xmm1"); return;
        case R_XMM2: printf("xmm2"); return;
        case R_XMM3: printf("xmm3"); return;
        case R_XMM4: printf("xmm4"); return;
        case R_XMM5: printf("xmm5"); return;
        case R_XMM6: printf("xmm6"); return;
        case R_XMM7: printf("xmm7"); return;
        }
    }
    fail("unrecognized machine register %d", mreg);
}

static void dump_arg(AsmInstr ai, int i) {
    switch (ai.arg_t[i]) {
    case AP_NONE: return;
    case AP_I64: printf("$%lld", ai.arg[i].i64); return;
    case AP_F32: printf("$%f", ai.arg[i].f32); return;
    case AP_F64: printf("$%lf", ai.arg[i].f64); return;
    case AP_SYM:
        printf("%s", Ident_to_str(ai.arg[i].sym.ident));
        if (ai.arg[i].sym.is_got)
            printf("@GOTPCREL");
        else if (ai.arg[i].sym.offset)
            printf("%+d", ai.arg[i].sym.offset);
        printf("(%%rip)");
        return;
    case AP_MREG:
        if (ai.arg[i].mreg.is_deref && ai.arg[i].mreg.offset)
            printf("%d", ai.arg[i].mreg.offset);
        if (ai.arg[i].mreg.is_deref) printf("(");
        dump_mreg(ai.arg[i].mreg.mreg, ai.arg[i].mreg.size);
        if (ai.arg[i].mreg.is_deref) printf(")");
        return;
    case AP_VREG: printf("%%.%u", ai.arg[i].vreg); return;
    case AP_STK_ARG: printf("%%.stk.%u", ai.arg[i].offset); return;
    case AP_PREV_STK_ARG: printf("%%.pstk.%u", ai.arg[i].offset); return;
    case AP_ALLOC: printf("%%.alloc.%u", ai.arg[i].offset); return;
    }
    fail("unknown arg type");
}

void dump_x64(AsmFunc *f) {
    uint32_t i, lb = 0;
    const char *s;
    AsmInstr ai;

    for (i = 0; f->instr[i].t; ++i) {
        while (f->label[lb].offset == i &&
               !Ident_eq(f->label[lb].ident, empty_ident)) {
            s = Ident_to_str(f->label[lb].ident);
            printf("%s%s:\n", s[0] == '@' ? "." : "", s+1);
            lb++;
        }
        ai = f->instr[i];
        assert(ai.t < countof(op_table) - 1);
        printf("    %s", op_table[ai.t]);
        dump_sz(ai.size);
        printf(" ");
        if (ai.arg_t[0] != AP_NONE) {
            dump_arg(ai, 0);
            if (ai.arg_t[1] != AP_NONE) {
                printf(", ");
                dump_arg(ai, 1);
            }
        }
        printf("\n");
    }
}

static AsmFunc asm_func;

static struct {
    FuncDef fd;
    uint32_t instr_cnt; /* AsmFunc.instr */
    uint32_t label_cnt; /* AsmFunc.label */
    int ret_ptr_alloc_offset;
} ctx;

#define MREG(r,sz) AP_MREG, .mreg=mreg(X64_SZ_##sz, r, 0, 0)
#define RAX MREG(R_RAX,Q)
#define RSP MREG(R_RSP,Q)
#define RBP MREG(R_RBP,Q)
#define RDI MREG(R_RDI,Q)
#define RSI MREG(R_RSI,Q)
#define RDX MREG(R_RDX,Q)
#define RCX MREG(R_RCX,Q)
#define R8  MREG(R_R8 ,Q)
#define R9  MREG(R_R9 ,Q)
#define R10 MREG(R_R10,Q)
#define R11 MREG(R_R11,Q)

#define I64(v) AP_I64, .i64=(v)
#define ALLOC(n) AP_ALLOC, .offset=(n)
#define MREG_OFF(r,sz,off) AP_MREG, .mreg=mreg(X64_SZ_##sz, (r), 1, (off))
#define PREV_STK_ARG(off) MREG_OFF(R_RBP, Q, 16+(off))

/* each rN will be expanded to two args */
#define EMIT1(op,sz,r0) _EMIT1(op,sz,r0)
#define EMIT2(op,sz,r0,r1) _EMIT2(op,sz,r0,r1)

#define EMIT0(op,sz)                                        \
    do {                                                    \
        asm_func.instr[ctx.instr_cnt].t = A_##op;           \
        asm_func.instr[ctx.instr_cnt].size = X64_SZ_##sz;   \
        ctx.instr_cnt++;                                    \
        assert(ctx.instr_cnt < countof(asm_func.instr));    \
    } while (0)

#define _EMIT1(op,sz,t0,r0)                                 \
    do {                                                    \
        asm_func.instr[ctx.instr_cnt].t = A_##op;           \
        asm_func.instr[ctx.instr_cnt].size = X64_SZ_##sz;   \
        asm_func.instr[ctx.instr_cnt].arg_t[0] = t0;        \
        asm_func.instr[ctx.instr_cnt].arg[0]r0;             \
        ctx.instr_cnt++;                                    \
        assert(ctx.instr_cnt < countof(asm_func.instr));    \
    } while (0)

#define _EMIT2(op,sz,t0,r0,t1,r1)                           \
    do {                                                    \
        asm_func.instr[ctx.instr_cnt].t = A_##op;           \
        asm_func.instr[ctx.instr_cnt].size = X64_SZ_##sz;   \
        asm_func.instr[ctx.instr_cnt].arg_t[0] = t0;        \
        asm_func.instr[ctx.instr_cnt].arg[0]r0;             \
        asm_func.instr[ctx.instr_cnt].arg_t[1] = t1;        \
        asm_func.instr[ctx.instr_cnt].arg[1]r1;             \
        ctx.instr_cnt++;                                    \
        assert(ctx.instr_cnt < countof(asm_func.instr));    \
    } while (0)

static struct MReg mreg(int size, int mreg, int is_deref, int offset) {
    struct MReg r;
    r.size = size;
    r.mreg = mreg;
    r.is_deref = is_deref;
    r.offset = offset;
    return r;
}

static void emit_label(Ident ident) {
    asm_func.label[ctx.label_cnt].ident = ident;
    asm_func.label[ctx.label_cnt].offset = ctx.instr_cnt;
    ctx.label_cnt++;
    assert(ctx.label_cnt < countof(asm_func.label));
}

typedef struct ClassifyResult {
    enum {
        P_NO_CLASS, /* ignored for passing */
        P_MEMORY,
        P_SSE,
        P_INTEGER
    };
    uint8_t fst; /* first eight bytes */
    uint8_t snd; /* second */
} ClassifyResult;

static int classify_visit(uint32_t, Type, ClassifyResult *);

static int classify_visit_struct(uint32_t offset, ArrType *sb,
                                 ClassifyResult *r) {
    int i;
    uint32_t j, align, size;
    for (i = 0; sb[i].t.t != TP_UNKNOWN; ++i) {
        align = 1u << Type_log_align(sb[i].t);
        size = Type_size(sb[i].t);
        if (i != 0)
            offset = (offset + align - 1) & ~(align - 1);
        for (j = 0; j < sb[i].count; ++j) {
            if (!classify_visit(offset, sb[i].t, r))
                return 0;
            offset += size;
        }
    }
    return 1;
}

static int classify_visit(uint32_t offset, Type t, ClassifyResult *r) {
    uint32_t align;
    uint32_t size;
    uint8_t *p;
    AgType *ag;
    int i;

    align = 1u << Type_log_align(t);
    size = Type_size(t);
    if (offset & (align - 1)) {
        r->fst = P_MEMORY;
        return 0; /* early exit */
    }
    p = offset < 8 ? &r->fst : &r->snd;

    switch (t.t) {
    case TP_W: case TP_L:
    case TP_B: case TP_H:
    case TP_SB: case TP_UB: case TP_SH: case TP_UH:
        *p = P_INTEGER;
        return 1;
    case TP_S: case TP_D:
        if (*p == P_NO_CLASS)
            *p = P_SSE;
        return 1;
    case TP_AG:
        break;
    default:
        fail("unrecognized TYPE");
        return 0; /* unreachable */
    }

    ag = AgType_get(t);
    if (ag->is_opaque) {
        /* ABI doc doesn't mention this,
           but I guess opaque should be treated as char array */
        *p = P_INTEGER;
        if (offset < 8 && size >= 8)
            r->snd = P_INTEGER;
        return 1;
    } else if (ag->is_union) {
        for (i = 0; ag->u.ub[i]; ++i)
            if (!classify_visit_struct(offset, ag->u.ub[i], r))
                return 0;
        return 1;
    } else {
        return classify_visit_struct(offset, ag->u.sb, r);
    }
}

static ClassifyResult classify(Type t) {
    ClassifyResult r = {0};
    if (Type_size(t) > 16) {
        r.fst = P_MEMORY;
        return r;
    }
    classify_visit(0, t, &r);
    return r;
}

static void emit_prologue(void) {
    static uint8_t int_regs[] = {R_RDI, R_RSI, R_RDX, R_RCX, R_R8, R_R9};
    static uint8_t sse_regs[] = {
        R_XMM0, R_XMM1, R_XMM2, R_XMM3, R_XMM4, R_XMM5, R_XMM6, R_XMM7};
    uint8_t used_int_regs = 0, used_sse_regs = 0;
    uint8_t ir_cnt, sr_cnt, use_stack;
    uint8_t reg;
    int i, j;
    uint32_t prev_stk_arg_size = 0;
    uint32_t copied_sz, tp_sz;
    ClassifyResult cr;

    emit_label(ctx.fd.ident);
    EMIT1(PUSH, Q, RBP);
    EMIT2(MOV, Q, RSP, RBP);
    EMIT2(SUB, Q, I64(0), RSP); /* size to be updated later */

    if (ctx.fd.ret_t.t != TP_NONE) {
        cr = classify(ctx.fd.ret_t);
        if (cr.fst == P_MEMORY) {
            EMIT2(MOV, Q, RDI, ALLOC(asm_func.alloc_sz));
            ctx.ret_ptr_alloc_offset = asm_func.alloc_sz;
            used_int_regs++;
            asm_func.alloc_sz += 8;
        }
    }

    for (i = 0; ctx.fd.params[i].t.t != TP_UNKNOWN; ++i) {
        check(!(i == 0 && ctx.fd.params[i].t.t == TP_NONE),
              "env params not supported"); /* TODO: support env */
        use_stack = (used_int_regs == countof(int_regs) &&
                     used_sse_regs == countof(sse_regs));
        if (!use_stack) {
            cr = classify(ctx.fd.params[i].t);
            ir_cnt = sr_cnt = 0;
            use_stack = cr.fst == P_MEMORY;
            if (!use_stack) {
                if (cr.fst == P_INTEGER) ir_cnt++;
                else if (cr.fst == P_SSE) sr_cnt++;
                if (cr.snd == P_INTEGER) ir_cnt++;
                else if (cr.snd == P_SSE) sr_cnt++;
                use_stack =
                    used_int_regs + ir_cnt > countof(int_regs) ||
                    used_sse_regs + sr_cnt > countof(sse_regs);
            }
        }

        if (!use_stack) {
            /* use regs */
            /* TODO: record params[i] => ALLOC(alloc_sz)
             * printf(">>> %s: %s => ALLOC(%u)\n",
             *       Ident_to_str(ctx.fd.ident),
             *       Ident_to_str(ctx.fd.params[i].ident),
             *       asm_func.alloc_sz); */
            for (j = 0; j < 2; ++j) {
                /* RAX: placeholder */
                if (((uint8_t *) &cr)[j] == P_INTEGER) {
                    reg = int_regs[used_int_regs++];
                    EMIT2(MOV, Q, RAX, ALLOC(asm_func.alloc_sz));
                } else if (((uint8_t *) &cr)[j] == P_SSE) {
                    reg = sse_regs[used_sse_regs++];
                    EMIT2(MOVS, D, RAX, ALLOC(asm_func.alloc_sz));
                } else continue;
                asm_func.alloc_sz += 8;
                /* fix placeholder RAX */
                asm_func.instr[ctx.instr_cnt - 1].arg[0].mreg.mreg = reg;
                asm_func.instr[ctx.instr_cnt - 1].arg[0].mreg.size =
                    asm_func.instr[ctx.instr_cnt - 1].size;
            }
        } else {
            /* use stack */
            /* TODO: record params[i] => ALLOC(alloc_sz)
             * printf(">>> %s: %s => PREV_STK_ARG(%u) => ALLOC(%u)\n",
             *       Ident_to_str(ctx.fd.ident),
             *       Ident_to_str(ctx.fd.params[i].ident),
             *       prev_stk_arg_size, asm_func.alloc_sz); */
            if (ctx.fd.params[i].t.t == TP_AG) {
                /* aggregate: IR values are actually addresses */
                EMIT2(LEA, Q,
                      ALLOC(asm_func.alloc_sz + 8),
                      ALLOC(asm_func.alloc_sz));
                asm_func.alloc_sz += 8;
            }
            /* copy to current frame */
            copied_sz = 0;
            tp_sz = Type_size(ctx.fd.params[i].t);
            while (tp_sz - copied_sz >= 8) {
                EMIT2(MOV, Q,
                      PREV_STK_ARG(prev_stk_arg_size + copied_sz),
                      ALLOC(asm_func.alloc_sz + copied_sz));
                copied_sz += 8;
            }
            while (tp_sz - copied_sz >= 4) {
                EMIT2(MOV, L,
                      PREV_STK_ARG(prev_stk_arg_size + copied_sz),
                      ALLOC(asm_func.alloc_sz + copied_sz));
                copied_sz += 4;
            }
            while (tp_sz - copied_sz >= 2) {
                EMIT2(MOV, W,
                      PREV_STK_ARG(prev_stk_arg_size + copied_sz),
                      ALLOC(asm_func.alloc_sz + copied_sz));
                copied_sz += 2;
            }
            while (tp_sz - copied_sz >= 1) {
                EMIT2(MOV, B,
                      PREV_STK_ARG(prev_stk_arg_size + copied_sz),
                      ALLOC(asm_func.alloc_sz + copied_sz));
                copied_sz += 1;
            }

            prev_stk_arg_size = (prev_stk_arg_size + tp_sz + 7) & ~7;
            asm_func.alloc_sz = (asm_func.alloc_sz + tp_sz + 7) & ~7;
        }
    }
}

AsmFunc *isel_simple_x64(FuncDef *fd) {
    memset(&asm_func, 0, sizeof(asm_func));
    memset(&ctx, 0, sizeof(ctx));
    ctx.fd = *fd;

    emit_prologue();
    /* TODO: isel_simple_x64 */

    asm_func.instr[ctx.instr_cnt].t = A_UNKNOWN;
    asm_func.label[ctx.label_cnt].ident = empty_ident;
    return &asm_func;
}
