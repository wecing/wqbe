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
    const char *s;
    switch (ai.arg_t[i]) {
    case AP_NONE: return;
    case AP_I64: printf("$%lld", ai.arg[i].i64); return;
    case AP_F32: printf("$%f", ai.arg[i].f32); return;
    case AP_F64: printf("$%lf", ai.arg[i].f64); return;
    case AP_SYM:
        s = Ident_to_str(ai.arg[i].sym.ident);
        printf("%s%s", s[0] == '@' ? "." : "", s+1);
        if (ai.t == A_JMP || ai.t == A_JNE)
            return;
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
    int32_t ret_ptr_alloc_offset;

    struct {
        Ident ident;
        uint32_t offset; /* byte offset for AP_ALLOC */
    } tmp[1024]; /* 8KB */
    uint32_t tmp_cnt;
} ctx;

static void record_tmp(Ident ident, uint32_t offset) {
    assert(ctx.tmp_cnt < countof(ctx.tmp));
    ctx.tmp[ctx.tmp_cnt].ident = ident;
    ctx.tmp[ctx.tmp_cnt].offset = offset;
    ctx.tmp_cnt++;
}

static uint32_t find_or_alloc_tmp(Ident ident) {
    uint32_t i, offset;
    for (i = 0; i < ctx.tmp_cnt; ++i)
        if (Ident_eq(ident, ctx.tmp[i].ident))
            return ctx.tmp[i].offset;
    offset = asm_func.alloc_sz;
    asm_func.alloc_sz += 8;
    record_tmp(ident, offset);
    return offset;
}

#define MREG(r,sz) AP_MREG, .mreg=mreg(X64_SZ_##sz,r,0,0)
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
#define XMM0 MREG(R_XMM0,D)
#define FAKE MREG(R_END,Q)

#define I64(v) AP_I64, .i64=(v)
#define ALLOC(n) AP_ALLOC, .offset=(n)
#define SYM(id) AP_SYM, .sym=msym(id,0,0)
#define SYM_GOT(id) AP_SYM, .sym=msym(id,1,0)
#define SYM_OFF(id,off) AP_SYM, .sym=msym(id,0,off)
#define MREG_OFF(r,off) AP_MREG, .mreg=mreg(X64_SZ_Q,(r),1,(off))
#define PREV_STK_ARG(off) MREG_OFF(R_RBP, 16+(off))
#define ARG(t,a) (t), =(a)

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

#define LAST_INSTR (asm_func.instr[ctx.instr_cnt - 1])

static struct MSym msym(Ident ident, int is_got, int offset) {
    struct MSym r;
    r.ident = ident;
    r.is_got = is_got;
    r.offset = offset;
    return r;
}

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
            record_tmp(ctx.fd.params[i].ident, asm_func.alloc_sz);
            for (j = 0; j < 2; ++j) {
                if (((uint8_t *) &cr)[j] == P_INTEGER) {
                    reg = int_regs[used_int_regs++];
                    EMIT2(MOV, Q, FAKE, ALLOC(asm_func.alloc_sz));
                } else if (((uint8_t *) &cr)[j] == P_SSE) {
                    reg = sse_regs[used_sse_regs++];
                    EMIT2(MOVS, D, FAKE, ALLOC(asm_func.alloc_sz));
                } else continue;
                asm_func.alloc_sz += 8;
                LAST_INSTR.arg[0].mreg.mreg = reg;
                LAST_INSTR.arg[0].mreg.size = LAST_INSTR.size;
            }
        } else {
            /* use stack */
            record_tmp(ctx.fd.params[i].ident, asm_func.alloc_sz);
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

typedef struct VisitValueResult {
    uint8_t t; /* AP_xxx */
    AsmInstrArg a;
} VisitValueResult;

/* avail_mreg is not guaranteed to be used */
static VisitValueResult visit_value(Value v, uint8_t avail_mreg) {
    VisitValueResult r = {0};
    switch (v.t) {
    case V_CI:
        r.t = AP_I64;
        r.a.i64 = v.u.u64;
        return r;
    case V_CS:
        r.t = AP_F32;
        r.a.f32 = v.u.s;
        return r;
    case V_CD:
        r.t = AP_F64;
        r.a.f64 = v.u.d;
        return r;
    case V_CSYM:
    case V_CTHS:
        EMIT2(LEA, Q, SYM(v.u.global_ident), FAKE);
        LAST_INSTR.arg[1].mreg.mreg = avail_mreg;
        /* now the symbol address is at %avail_mreg. */
        r.t = AP_MREG;
        r.a.mreg = mreg(X64_SZ_Q, avail_mreg, 0, 0);
        return r;
    case V_TMP:
        /* allow visiting usage before def */
        r.t = AP_ALLOC;
        r.a.offset = find_or_alloc_tmp(v.u.tmp_ident);
        return r;
    default: break;
    }
    fail("unrecognized VALUE type");
    return r; /* unreachable */
}

static void isel_copy(Instr instr) {
    uint32_t tp_sz, copied_sz, d;
    VisitValueResult vvr;

    vvr = visit_value(instr.u.args[0], R_R10);
    if (instr.ret_t.t == TP_AG) {
        /* output of copy op */
        EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz),
              ALLOC(find_or_alloc_tmp(instr.ident)));
        /* actual coping */
        EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
        tp_sz = Type_size(instr.ret_t);
        copied_sz = 0;
        while (tp_sz - copied_sz >= 8) {
            EMIT2(MOV, Q, MREG_OFF(R_R10, copied_sz),
                  ALLOC(asm_func.alloc_sz + copied_sz));
            copied_sz += 8;
        }
        while (tp_sz - copied_sz >= 4) {
            EMIT2(MOV, L, MREG_OFF(R_R10, copied_sz),
                  ALLOC(asm_func.alloc_sz + copied_sz));
            copied_sz += 4;
        }
        while (tp_sz - copied_sz >= 2) {
            EMIT2(MOV, W, MREG_OFF(R_R10, copied_sz),
                  ALLOC(asm_func.alloc_sz + copied_sz));
            copied_sz += 2;
        }
        while (tp_sz - copied_sz >= 1) {
            EMIT2(MOV, B, MREG_OFF(R_R10, copied_sz),
                  ALLOC(asm_func.alloc_sz + copied_sz));
            copied_sz += 1;
        }
        asm_func.alloc_sz = (asm_func.alloc_sz + tp_sz + 7) & ~7;
    } else {
        d = find_or_alloc_tmp(instr.ident);
        switch (instr.ret_t.t) {
        case TP_W: EMIT2(MOV, L, ARG(vvr.t, vvr.a), ALLOC(d)); break;
        case TP_L: EMIT2(MOV, Q, ARG(vvr.t, vvr.a), ALLOC(d)); break;
        case TP_S: EMIT2(MOVS, S, ARG(vvr.t, vvr.a), ALLOC(d)); break;
        case TP_D: EMIT2(MOVS, D, ARG(vvr.t, vvr.a), ALLOC(d)); break;
        default:
            fail("unexpected copy type");
        }
    }
}

static void isel_phi(Instr instr) {
    (void)instr;
    fail("unexpected phi op");
}

static void isel_hlt(Instr instr) {
    (void)instr;
    EMIT2(MOV, Q, I64(0), R10);
    EMIT2(MOV, Q, I64(0), MREG_OFF(R_R10, 0)); /* segfault */
}

static void isel_jmp(Instr instr) {
    EMIT1(JMP, NONE, SYM(instr.u.jump.dst));
}

static void isel_jnz(Instr instr) {
    /* QBE requires cond to be of i32 type;
       i64 is also allowed but higher 32 bits are discarded. */
    VisitValueResult vvr;
    vvr = visit_value(instr.u.jump.v, R_R10);
    EMIT2(CMP, L, ARG(vvr.t, vvr.a), I64(0));
    EMIT1(JNE, NONE, SYM(instr.u.jump.dst));
    EMIT1(JMP, NONE, SYM(instr.u.jump.dst_else));
}

static void isel_ret(Instr instr) {
    if (instr.u.jump.v.t != V_UNKNOWN) {
        VisitValueResult vvr = visit_value(instr.u.jump.v, R_R10);
        if (ctx.fd.ret_t.t == TP_AG) {
            ClassifyResult cr = classify(ctx.fd.ret_t);
            if (cr.fst == P_MEMORY) {
                uint32_t tp_sz = Type_size(ctx.fd.ret_t);
                uint32_t copied_sz = 0;
                /* RAX: required by ABI */
                EMIT2(MOV, Q, ALLOC(ctx.ret_ptr_alloc_offset), RAX);
                EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
                while (tp_sz - copied_sz >= 8) {
                    EMIT2(MOV, Q,
                          MREG_OFF(R_R10, copied_sz),
                          MREG_OFF(R_RAX, copied_sz));
                    copied_sz += 8;
                }
                while (tp_sz - copied_sz >= 4) {
                    EMIT2(MOV, L,
                          MREG_OFF(R_R10, copied_sz),
                          MREG_OFF(R_RAX, copied_sz));
                    copied_sz += 4;
                }
                while (tp_sz - copied_sz >= 2) {
                    EMIT2(MOV, W,
                          MREG_OFF(R_R10, copied_sz),
                          MREG_OFF(R_RAX, copied_sz));
                    copied_sz += 2;
                }
                while (tp_sz - copied_sz >= 1) {
                    EMIT2(MOV, B,
                          MREG_OFF(R_R10, copied_sz),
                          MREG_OFF(R_RAX, copied_sz));
                    copied_sz += 1;
                }
            } else {
                int i;
                int used_int_regs = 0, used_sse_regs = 0;
                uint8_t *crp = (void*) &cr;
                EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
                /* TODO: this is not always correct.
                   e.g. the return type could be a struct {char[7]}, placed at
                   0x7; movq from 0x7 is misaligned access. a better solution
                   might be to copy the result into an on-stack well-aligned
                   place, then move into %rax/%rdi/%xmm0/%xmm1. */
                for (i = 0; i < 2; ++i) {
                    if (crp[i] == P_SSE) {
                        EMIT2(MOVS, D, MREG_OFF(R_R10, i * 8), FAKE);
                        LAST_INSTR.arg[1].mreg.mreg =
                            used_sse_regs == 0 ? R_XMM0 : R_XMM1;
                        LAST_INSTR.arg[1].mreg.size = LAST_INSTR.size;
                        used_sse_regs++;
                    } else if (crp[i] == P_INTEGER) {
                        EMIT2(MOV, Q, MREG_OFF(R_R10, i * 8), FAKE);
                        LAST_INSTR.arg[1].mreg.mreg =
                            used_int_regs == 0 ? R_RAX : R_RDX;
                        used_int_regs++;
                    }
                }
            }
        } else {
            switch (ctx.fd.ret_t.t) {
#define SRC ARG(vvr.t, vvr.a)
            case TP_W: EMIT2(MOV, L, SRC, MREG(R_RAX, L)); break;
            case TP_L: EMIT2(MOV, Q, SRC, RAX); break;
            case TP_S: EMIT2(MOVS, S, SRC, XMM0); break;
            case TP_D: EMIT2(MOVS, D, SRC, XMM0); break;
            case TP_SB: case TP_UB: EMIT2(MOV, B, SRC, MREG(R_RAX, B)); break;
            case TP_SH: case TP_UH: EMIT2(MOV, W, SRC, MREG(R_RAX, W)); break;
#undef SRC
            default:
                fail("FUNCDEF must return [ABITY]");
            }
        }
    }
    EMIT2(MOV, Q, RBP, RSP);
    EMIT1(POP, Q, RBP);
    EMIT0(RET, NONE);
}

static void isel(Instr instr) {
    static const char *op_name[] = {
        0,
#define I(up,low) #low,
#include "instr.inc"
#undef I
        0
    };

    switch (instr.t) {
    case I_ADD:
    case I_AND:
    case I_DIV:
    case I_MUL:
    case I_NEG:
    case I_OR:
    case I_REM:
    case I_SAR:
    case I_SHL:
    case I_SHR:
    case I_SUB:
    case I_UDIV:
    case I_UREM:
    case I_XOR:
        /* TODO: implement isel: arith and bits */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_ALLOC16:
    case I_ALLOC4:
    case I_ALLOC8:
    case I_BLIT:
    case I_LOADD:
    case I_LOADL:
    case I_LOADS:
    case I_LOADSB:
    case I_LOADSH:
    case I_LOADSW:
    case I_LOADUB:
    case I_LOADUH:
    case I_LOADUW:
    case I_LOADW:
    case I_STOREB:
    case I_STORED:
    case I_STOREH:
    case I_STOREL:
    case I_STORES:
    case I_STOREW:
        /* TODO: implement isel: memory */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_CEQD:
    case I_CEQL:
    case I_CEQS:
    case I_CEQW:
    case I_CGED:
    case I_CGES:
    case I_CGTD:
    case I_CGTS:
    case I_CLED:
    case I_CLES:
    case I_CLTD:
    case I_CLTS:
    case I_CNED:
    case I_CNEL:
    case I_CNES:
    case I_CNEW:
    case I_COD:
    case I_COS:
    case I_CSGEL:
    case I_CSGEW:
    case I_CSGTL:
    case I_CSGTW:
    case I_CSLEL:
    case I_CSLEW:
    case I_CSLTL:
    case I_CSLTW:
    case I_CUGEL:
    case I_CUGEW:
    case I_CUGTL:
    case I_CUGTW:
    case I_CULEL:
    case I_CULEW:
    case I_CULTL:
    case I_CULTW:
    case I_CUOD:
    case I_CUOS:
        /* TODO: implement isel: cmp */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_DTOSI:
    case I_DTOUI:
    case I_EXTS:
    case I_EXTSB:
    case I_EXTSH:
    case I_EXTSW:
    case I_EXTUB:
    case I_EXTUH:
    case I_EXTUW:
    case I_SLTOF:
    case I_ULTOF:
    case I_STOSI:
    case I_STOUI:
    case I_SWTOF:
    case I_UWTOF:
    case I_TRUNCD:
        /* TODO: implement isel: conv */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_CAST:
        /* TODO: implement isel: cast & copy */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_COPY: isel_copy(instr); return;
    case I_CALL:
        /* TODO: implement isel: call */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_VASTART:
    case I_VAARG:
        /* TODO: implement isel: vastart & vaarg */
        fail("not implemented: %s", op_name[instr.t]);
        return;
    case I_PHI: isel_phi(instr); return;
    case I_HLT: isel_hlt(instr); return;
    case I_JMP: isel_jmp(instr); return;
    case I_JNZ: isel_jnz(instr); return;
    case I_RET: isel_ret(instr); return;
    }
    fail("unrecognized instr type %d", instr.t);
}

AsmFunc *isel_simple_x64(FuncDef *fd) {
    uint16_t blk_id;
    uint32_t instr_id;
    Block blk;
    Instr instr;

    memset(&asm_func, 0, sizeof(asm_func));
    memset(&ctx, 0, sizeof(ctx));
    ctx.fd = *fd;

    emit_prologue();

    blk_id = ctx.fd.blk_id;
    while (blk_id) {
        blk = *Block_get(blk_id);
        blk_id = blk.next_id;

        emit_label(blk.ident);

        instr_id = blk.instr_id;
        while (instr_id) {
            instr = *Instr_get(instr_id);
            instr_id = instr.next_id;
            isel(instr);
        }
        isel(*Instr_get(blk.jump_id));
    }

    asm_func.instr[ctx.instr_cnt].t = A_UNKNOWN;
    asm_func.label[ctx.label_cnt].ident = empty_ident;
    asm_func.instr[2].arg[0].i64 = asm_func.alloc_sz; /* fix sub $0, %rsp */
    return &asm_func;
}
