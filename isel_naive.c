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
        case R_XMM8: printf("xmm8"); return;
        case R_XMM9: printf("xmm9"); return;
        case R_XMM10: printf("xmm10"); return;
        case R_XMM11: printf("xmm11"); return;
        case R_XMM12: printf("xmm12"); return;
        case R_XMM13: printf("xmm13"); return;
        case R_XMM14: printf("xmm14"); return;
        case R_XMM15: printf("xmm15"); return;
        }
    }
    fail("unrecognized machine register %d; size = %d", mreg, size);
}

static void dump_label(Ident ident) {
    const char *s = Ident_to_str(ident);
    printf("%s%s", s[0] == '@' ? "." : "_", s+1);
}

static void dump_arg(AsmInstr ai, int i) {
    switch (ai.arg_t[i]) {
    case AP_NONE: return;
    case AP_I64: printf("$%lld", ai.arg[i].i64); return;
    case AP_F32: printf("$%f", ai.arg[i].f32); return;
    case AP_F64: printf("$%lf", ai.arg[i].f64); return;
    case AP_SYM:
        dump_label(ai.arg[i].sym.ident);
        if (ai.t == A_JMP || ai.t == A_JNE ||
            ai.t == A_JE || ai.t == A_JL || ai.t == A_CALL)
            return;
        if (ai.arg[i].sym.is_got)
            printf("@GOTPCREL");
        else if (ai.arg[i].sym.offset)
            printf("%+d", ai.arg[i].sym.offset);
        printf("(%%rip)");
        return;
    case AP_MREG:
        if (ai.t == A_CALL)
            printf("*"); /* callq *%rax, callq *32(%rbp), etc */
        if (ai.arg[i].mreg.is_deref && ai.arg[i].mreg.offset)
            printf("%d", ai.arg[i].mreg.offset);
        if (ai.arg[i].mreg.is_deref) printf("(");
        dump_mreg(ai.arg[i].mreg.mreg, ai.arg[i].mreg.size);
        if (ai.arg[i].mreg.is_deref) printf(")");
        return;
    case AP_VREG: printf("%%.%u", ai.arg[i].vreg); return;
    case AP_ALLOC: printf("%%.alloc.%u", ai.arg[i].offset); return;
    }
    fail("unknown arg type");
}

void dump_x64(AsmFunc *f) {
    uint32_t i, lb = 0;
    AsmInstr ai;

    printf(".text\n");
    printf(".globl ");
    dump_label(f->label[0].ident);
    printf("\n");

    for (i = 0; f->instr[i].t; ++i) {
        while (f->label[lb].offset == i &&
               !Ident_eq(f->label[lb].ident, empty_ident)) {
            dump_label(f->label[lb].ident);
            printf(":\n");
            lb++;
        }
        ai = f->instr[i];
        assert(ai.t < countof(op_table) - 1);
        printf("    %s", op_table[ai.t]);
        dump_sz(ai.size);
        if (ai.arg_t[0] != AP_NONE) {
            printf(" ");
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

    uint8_t is_first_blk;

    /* on x64, va_list is defined as:

       typedef struct {
           unsigned int gp_offset;
           unsigned int fp_offset;
           void *overflow_arg_area;
           void *reg_save_area;
       } va_list[1]; */

    uint32_t gp_offset;
    uint32_t fp_offset;
    /* overflow_arg_area is just %rbp+16 */
    uint32_t reg_save_area; /* ALLOC offset */
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
#define XMM8 MREG(R_XMM8,D)
#define XMM9 MREG(R_XMM9,D)
#define EAX MREG(R_RAX,L)
#define EDX MREG(R_RDX,L)
#define ECX MREG(R_RCX,L)
#define R11D MREG(R_R11,L)
#define FAKE MREG(R_END,Q)

#define I64(v) AP_I64, .i64=(v)
#define F32(v) AP_F32, .f32=(v)
#define F64(v) AP_F64, .f64=(v)
#define ALLOC(n) AP_ALLOC, .offset=(n)
#define SYM(id) AP_SYM, .sym=msym(id,0,0)
#define SYM_GOT(id) AP_SYM, .sym=msym(id,1,0)
#define SYM_OFF(id,off) AP_SYM, .sym=msym(id,0,off)
#define MREG_OFF(r,off) AP_MREG, .mreg=mreg(X64_SZ_Q,(r),1,(off))
#define PREV_STK_ARG(off) MREG_OFF(R_RBP, 16+(off))
#define STK_ARG(off) MREG_OFF(R_RSP, off)
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

static AsmInstrArg blit_offset(uint8_t t, AsmInstrArg a, uint32_t off) {
    switch (t) {
    case AP_MREG:
        a.mreg.offset += off;
        return a;
    case AP_ALLOC:
        a.offset += off;
        return a;
    }
    fail("unexpected AsmInstrArg type");
    return a; /* unreachable */
}

#define blit(r0,r1,sz) _blit(r0,r1,sz)
#define _blit(t0,r0,t1,r1,sz) \
    do { \
        AsmInstrArg _blit_from = {0}; \
        AsmInstrArg _blit_to = {0}; \
        _blit_from r0; \
        _blit_to r1; \
        blit_impl((t0), _blit_from, (t1), _blit_to, sz); \
    } while (0)

/* note: from/to shall not use R11. */
static void blit_impl(uint8_t from_t, AsmInstrArg from,
                      uint8_t to_t, AsmInstrArg to,
                      uint32_t sz) {
#define SRC ARG(from_t, blit_offset(from_t, from, copied_sz))
#define DST ARG(to_t, blit_offset(to_t, to, copied_sz))
    uint32_t copied_sz = 0;
    while (sz - copied_sz >= 8) {
        EMIT2(MOV, Q, SRC, DST);
        copied_sz += 8;
    }
    while (sz - copied_sz >= 4) {
        EMIT2(MOV, L, SRC, DST);
        copied_sz += 4;
    }
    while (sz - copied_sz >= 2) {
        EMIT2(MOV, W, SRC, DST);
        copied_sz += 2;
    }
    while (sz - copied_sz >= 1) {
        EMIT2(MOV, B, SRC, DST);
        copied_sz += 1;
    }
#undef DST
#undef SRC
}

static void emit_reg_save(uint8_t used_int_regs, uint8_t used_sse_regs) {
    static uint8_t int_regs[] = {R_RDI, R_RSI, R_RDX, R_RCX, R_R8, R_R9};
    static uint8_t sse_regs[] = {
        R_XMM0, R_XMM1, R_XMM2, R_XMM3, R_XMM4, R_XMM5, R_XMM6, R_XMM7};
    int blk_id = ctx.fd.blk_id, instr_id = 0;
    Block blk;
    Instr instr;
    char buf[100];
    Ident skip_label;
    static int buf_suffix = 0;

    while (blk_id) {
        blk = *Block_get(blk_id);
        blk_id = blk.next_id;
        instr_id = blk.instr_id;
        while (instr_id) {
            instr = *Instr_get(instr_id);
            instr_id = instr.next_id;
            if (instr.t == I_VASTART)
                goto proceed;
        }
    }
    return;

proceed:
    ctx.gp_offset = used_int_regs * 8;
    ctx.fp_offset = countof(int_regs) * 8 + used_sse_regs * 16;
    ctx.reg_save_area = asm_func.alloc_sz;
    asm_func.alloc_sz += countof(int_regs) * 8 + countof(sse_regs) * 16;
    while (used_int_regs < countof(int_regs)) {
        EMIT2(MOV, Q, FAKE, ALLOC(ctx.reg_save_area + used_int_regs * 8));
        LAST_INSTR.arg[0].mreg.mreg = int_regs[used_int_regs];
        used_int_regs++;
    }
    sprintf(buf, "@wqbe_reg_save_end_%d", buf_suffix++);
    skip_label = Ident_from_str(buf);
    EMIT2(CMP, B, I64(0), MREG(R_RAX, B));
    EMIT1(JE, NONE, SYM(skip_label));
    while (used_sse_regs < countof(sse_regs)) {
        EMIT2(MOVS, D, FAKE,
              ALLOC(ctx.reg_save_area + countof(int_regs) * 8 +
                    used_sse_regs * 16));
        LAST_INSTR.arg[0].mreg.size = X64_SZ_D;
        LAST_INSTR.arg[0].mreg.mreg = sse_regs[used_sse_regs];
        used_sse_regs++;
    }
    emit_label(skip_label);
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
            uint32_t tp_sz = Type_size(ctx.fd.params[i].t);
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
            blit(PREV_STK_ARG(prev_stk_arg_size), ALLOC(asm_func.alloc_sz),
                 tp_sz);
            prev_stk_arg_size = (prev_stk_arg_size + tp_sz + 7) & ~7;
            asm_func.alloc_sz = (asm_func.alloc_sz + tp_sz + 7) & ~7;
        }
    }

    emit_reg_save(used_int_regs, used_sse_regs);
}

typedef struct VisitValueResult {
    uint8_t t; /* AP_xxx */
    AsmInstrArg a;
} VisitValueResult;

/* avail_mreg is not guaranteed to be used.

   in fact, it will only be used for getting global symbol addr, so:
   1. avail_mreg should always be an int reg;
   2. is avail_mreg is used, input Value is guaranteed not to be FP. */
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

#define arith_wlsd(op,ixop,fxop) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult x = visit_value(instr.u.args[0], R_R10); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT2(ixop, L, ARG(x.t, x.a), ALLOC(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT2(ixop, Q, ARG(x.t, x.a), ALLOC(dst)); \
        } else if (instr.ret_t.t == TP_S) { \
            EMIT2(MOV, S, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); /* R10 not used */ \
            EMIT2(fxop, S, ARG(x.t, x.a), ALLOC(dst)); \
        } else if (instr.ret_t.t == TP_D) { \
            EMIT2(MOV, D, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); /* R10 not used */ \
            EMIT2(fxop, D, ARG(x.t, x.a), ALLOC(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

#define arith_wl(op,xop) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult x = visit_value(instr.u.args[0], R_R10); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT2(xop, L, ARG(x.t, x.a), ALLOC(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT2(xop, Q, ARG(x.t, x.a), ALLOC(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

arith_wlsd(add, ADD, ADDS)
arith_wlsd(sub, SUB, SUBS)
arith_wlsd(mul, IMUL, MULS)

arith_wl(or, OR)
arith_wl(xor, XOR)
arith_wl(and, AND)

static void isel_div(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult x = visit_value(instr.u.args[0], R_RAX);
    if (instr.ret_t.t == TP_W) {
        EMIT2(MOV, L, ARG(x.t, x.a), EAX);
        x = visit_value(instr.u.args[1], R_R10);
        EMIT1(IDIV, L, ARG(x.t, x.a));
        EMIT2(MOV, L, EAX, ALLOC(dst));
    } else if (instr.ret_t.t == TP_L) {
        EMIT2(MOV, Q, ARG(x.t, x.a), RAX);
        x = visit_value(instr.u.args[1], R_R10);
        EMIT1(IDIV, Q, ARG(x.t, x.a));
        EMIT2(MOV, Q, RAX, ALLOC(dst));
    } else if (instr.ret_t.t == TP_S) {
        EMIT2(MOV, S, ARG(x.t, x.a), ALLOC(dst));
        x = visit_value(instr.u.args[1], R_R10); /* R10 not used */
        EMIT2(DIVS, S, ARG(x.t, x.a), ALLOC(dst));
    } else if (instr.ret_t.t == TP_D) {
        EMIT2(MOV, D, ARG(x.t, x.a), ALLOC(dst));
        x = visit_value(instr.u.args[1], R_R10); /* R10 not used */
        EMIT2(DIVS, D, ARG(x.t, x.a), ALLOC(dst));
    } else {
        fail("unexpected return type");
    }
}

#define int_div_rem(op,xop,r) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult x = visit_value(instr.u.args[0], R_RAX); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), EAX); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT1(xop, L, ARG(x.t, x.a)); \
            EMIT2(MOV, L, MREG(r, L), ALLOC(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), RAX); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT1(xop, Q, ARG(x.t, x.a)); \
            EMIT2(MOV, Q, MREG(r, Q), ALLOC(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

int_div_rem(udiv,DIV,R_RAX)
int_div_rem(rem,IDIV,R_RDX)
int_div_rem(urem,DIV,R_RDX)

#define shift_wl(op,xop) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult x = visit_value(instr.u.args[0], R_R10); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT2(MOV, B, ARG(x.t, x.a), MREG(R_RCX, B)); \
            EMIT2(xop, L, MREG(R_RCX, B), ALLOC(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), ALLOC(dst)); \
            x = visit_value(instr.u.args[1], R_R10); \
            EMIT2(MOV, B, ARG(x.t, x.a), MREG(R_RCX, B)); \
            EMIT2(xop, Q, MREG(R_RCX, B), ALLOC(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

shift_wl(sar, SAR)
shift_wl(shl, SHL)
shift_wl(shr, SHR)

static void isel_neg(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult vvr = visit_value(instr.u.args[0], R_R10);
    if (instr.ret_t.t == TP_W) {
        EMIT2(MOV, L, ARG(vvr.t, vvr.a), ALLOC(dst));
        EMIT1(NEG, L, ALLOC(dst));
    } else if (instr.ret_t.t == TP_L) {
        EMIT2(MOV, Q, ARG(vvr.t, vvr.a), ALLOC(dst));
        EMIT1(NEG, Q, ALLOC(dst));
    } else if (instr.ret_t.t == TP_S) {
        EMIT2(MOVS, S, ARG(vvr.t, vvr.a), ALLOC(dst));
        EMIT2(XOR, L, I64(1L << 31), ALLOC(dst));
    } else if (instr.ret_t.t == TP_D) {
        EMIT2(MOVS, D, ARG(vvr.t, vvr.a), ALLOC(dst));
        EMIT2(XOR, Q, I64(1L << 63), ALLOC(dst));
    } else {
        fail("unexpected return type");
    }
}

#define isel_alloc16 isel_alloc
#define isel_alloc4  isel_alloc
#define isel_alloc8  isel_alloc

static void isel_alloc(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    if (ctx.is_first_blk && instr.u.args[0].t == V_CI) {
        uint32_t sz = (instr.u.args[0].u.u64 + 7) & ~7;
        if (instr.t == I_ALLOC16)
            asm_func.alloc_sz = (asm_func.alloc_sz + 15) & ~15;
        EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz), ALLOC(dst));
        asm_func.alloc_sz += sz;
    } else {
        asm_func.has_dyn_alloc = 1;
        if (instr.u.args[0].t == V_CI) {
            uint32_t sz = (instr.u.args[0].u.u64 + 7) & ~7;
            if (instr.t == I_ALLOC16)
                sz += 8;
            EMIT2(SUB, Q, I64(sz), RSP);
        } else {
            VisitValueResult vvr = visit_value(instr.u.args[0], R_R10);
            EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
            EMIT2(ADD, Q, I64(7), R10);
            EMIT2(AND, Q, I64(~7), R10);
            if (instr.t == I_ALLOC16)
                EMIT2(ADD, Q, I64(8), R10);
            EMIT2(SUB, Q, R10, RSP);
        }
        EMIT2(MOV, Q, RSP, ALLOC(dst));
        if (instr.t == I_ALLOC16) {
            EMIT2(ADD, Q, I64(15), ALLOC(dst));
            EMIT2(AND, Q, I64(~15), ALLOC(dst));
        }
    }
}

static void isel_blit(Instr instr) {
    VisitValueResult src = visit_value(instr.u.args[0], R_R10);
    VisitValueResult dst = visit_value(instr.u.args[1], R_RAX);
    EMIT2(MOV, Q, ARG(src.t, src.a), R10);
    EMIT2(MOV, Q, ARG(dst.t, dst.a), RAX);
    blit(MREG_OFF(R_R10, 0), MREG_OFF(R_RAX, 0), instr.blit_sz);
}

#define load_mem_simple(op,xs) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult p = visit_value(instr.u.args[0], R_R11); \
        EMIT2(MOV, Q, ARG(p.t, p.a), R11); \
        EMIT2(MOVS, xs, MREG_OFF(R_R11, 0), ALLOC(dst)); \
    }

load_mem_simple(loadl, Q)
load_mem_simple(loads, S)
load_mem_simple(loadd, D)

#define load_mem_bhw(op,xqop,xqsz,xlop,xlsz) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult p = visit_value(instr.u.args[0], R_R11); \
        EMIT2(MOV, Q, ARG(p.t, p.a), R11); \
        if (instr.ret_t.t == TP_L) { \
            EMIT2(xqop, xqsz, MREG_OFF(R_R11, 0), MREG(R_R11, xqsz)); \
            EMIT2(MOV, Q, MREG(R_R11, Q), ALLOC(dst)); \
        } else { \
            EMIT2(xlop, xlsz, MREG_OFF(R_R11, 0), MREG(R_R11, xlsz)); \
            EMIT2(MOV, L, MREG(R_R11, L), ALLOC(dst)); \
        } \
    }

load_mem_bhw(loadsw, MOVSL, Q, MOV,   L)
load_mem_bhw(loaduw, MOV,   L, MOV,   L)
load_mem_bhw(loadsh, MOVSW, Q, MOVSW, L)
load_mem_bhw(loaduh, MOVZW, Q, MOVZW, L)
load_mem_bhw(loadsb, MOVSB, Q, MOVSB, L)
load_mem_bhw(loadub, MOVZB, Q, MOVZB, L)

#define isel_loadw isel_loadsw

#define store_mem(op,xs,tmp) \
    static void isel_##op(Instr instr) { \
        VisitValueResult v = visit_value(instr.u.args[0], tmp); \
        VisitValueResult p = visit_value(instr.u.args[1], R_R10); \
        EMIT2(MOV, xs, ARG(v.t, v.a), MREG(tmp, xs)); \
        EMIT2(MOV, Q, ARG(p.t, p.a), R10); \
        EMIT2(MOV, xs, MREG(tmp, xs), MREG_OFF(R_R10, 0)); \
    }

store_mem(storeb, B, R_R11)
store_mem(storeh, W, R_R11)
store_mem(storew, L, R_R11)
store_mem(storel, Q, R_R11)
store_mem(stores, S, R_XMM8)
store_mem(stored, D, R_XMM8)

#define cmp_int_impl(op,s,xs,xop) \
    static void isel_c##op##s(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        VisitValueResult x = visit_value(instr.u.args[0], R_R10); \
        VisitValueResult y = visit_value(instr.u.args[1], R_R11); \
        EMIT2(MOV, xs, I64(0), ALLOC(dst)); \
        EMIT2(MOV, xs, ARG(x.t, x.a), MREG(R_R10,xs)); \
        EMIT2(MOV, xs, ARG(y.t, y.a), MREG(R_R11,xs)); \
        EMIT2(CMP, xs, MREG(R_R11,xs), MREG(R_R10,xs)); \
        EMIT1(xop, NONE, ALLOC(dst)); \
    }
#define cmp_int(op,xop) \
    cmp_int_impl(op,w,L,xop) \
    cmp_int_impl(op,l,Q,xop)

/* eq/ne for fp needs special treatment.
   (ucomisd NaN, NaN) sets ZF=1 but (NaN cmp NaN) is false. */

#define cmp_sse_impl(op,s,xs,xop) \
    static void isel_c##op##s(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        /* visit_value: xmm8/xmm9 not used */ \
        VisitValueResult x = visit_value(instr.u.args[0], R_XMM8); \
        VisitValueResult y = visit_value(instr.u.args[1], R_XMM9); \
        EMIT2(MOV, xs, I64(0), ALLOC(dst)); \
        if (A_##xop == A_SETE || A_##xop == A_SETNE) \
            EMIT2(MOV, xs, I64(0), MREG(R_R11,xs)); \
        EMIT2(MOV, xs, ARG(x.t, x.a), MREG(R_XMM8,xs)); \
        EMIT2(MOV, xs, ARG(y.t, y.a), MREG(R_XMM9,xs)); \
        EMIT2(UCOMIS, xs, MREG(R_XMM9,xs), MREG(R_XMM8,xs)); \
        EMIT1(xop, NONE, ALLOC(dst)); \
        if (A_##xop == A_SETE) { \
            EMIT1(SETNP, NONE, MREG(R_R11,B)); \
            EMIT2(AND, xs, MREG(R_R11,xs), ALLOC(dst)); \
        } else if (A_##xop == A_SETNE) { \
            EMIT1(SETP, NONE, MREG(R_R11,B)); \
            EMIT2(OR, xs, MREG(R_R11,xs), ALLOC(dst)); \
        } \
    }
#define cmp_sse(op,xop) \
    cmp_sse_impl(op,s,S,xop) \
    cmp_sse_impl(op,d,D,xop)

cmp_int(eq, SETE)
cmp_int(ne, SETNE)
cmp_int(sle, SETLE)
cmp_int(slt, SETL)
cmp_int(sge, SETGE)
cmp_int(sgt, SETG)
cmp_int(ule, SETBE)
cmp_int(ult, SETB)
cmp_int(uge, SETAE)
cmp_int(ugt, SETA)

cmp_sse(eq, SETE)
cmp_sse(ne, SETNE)
cmp_sse(le, SETLE)
cmp_sse(lt, SETL)
cmp_sse(ge, SETGE)
cmp_sse(gt, SETG)
cmp_sse(o, SETNP)
cmp_sse(uo, SETP)

static void isel_truncd(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    EMIT2(MOVS, S, ARG(v.t, v.a), XMM8);
    EMIT2(CVTSS2S, D, XMM8, XMM8);
    EMIT2(MOVS, D, XMM8, ALLOC(dst));
}

static void isel_exts(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    EMIT2(MOVS, D, ARG(v.t, v.a), XMM8);
    EMIT2(CVTSD2S, S, XMM8, XMM8);
    EMIT2(MOVS, D, XMM8, ALLOC(dst));
}

static void isel_extsw(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    EMIT2(MOVSL, Q, ARG(v.t, v.a), R11);
    EMIT2(MOV, Q, R11, ALLOC(dst));
}

static void isel_extuw(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    EMIT2(MOV, L, ARG(v.t, v.a), R11D);
    EMIT2(MOV, Q, R11, ALLOC(dst));
}

#define ext_hb(op,xop) \
    static void isel_##op(Instr instr) { \
        uint32_t dst = find_or_alloc_tmp(instr.ident); \
        /* R10 unused */ \
        VisitValueResult v = visit_value(instr.u.args[0], R_R10); \
        EMIT2(MOV, Q, ARG(v.t, v.a), R10); \
        if (instr.ret_t.t == TP_W) \
            EMIT2(xop, L, ARG(v.t, v.a), ALLOC(dst)); \
        else \
            EMIT2(xop, Q, ARG(v.t, v.a), ALLOC(dst)); \
    }

ext_hb(extsh, MOVSW)
ext_hb(extuh, MOVZW)
ext_hb(extsb, MOVSB)
ext_hb(extub, MOVZB)

static void isel_stosi(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    if (instr.ret_t.t == TP_W) {
        EMIT2(CVTTSS2SI, L, ARG(v.t, v.a), R11D);
        EMIT2(MOV, L, R11D, ALLOC(dst));
    } else {
        EMIT2(CVTTSS2SI, Q, ARG(v.t, v.a), R11);
        EMIT2(MOV, Q, R11, ALLOC(dst));
    }
}

static void isel_stoui(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    if (instr.ret_t.t == TP_W) {
        EMIT2(CVTTSS2SI, Q, ARG(v.t, v.a), R11);
    } else {
        EMIT2(MOVS, S, ARG(v.t, v.a), XMM8);
        EMIT2(CVTTSS2SI, Q, XMM8, R11);
        EMIT2(MOV, Q, R11, R10);
        EMIT2(SAR, Q, I64(63), R10);
        EMIT2(ADDS, S, F64(-9223372036854775808.0), XMM8);
        EMIT2(CVTTSS2SI, Q, XMM8, RAX);
        EMIT2(AND, Q, R10, RAX);
        EMIT2(OR, Q, RAX, R11);
    }
    EMIT2(MOV, Q, R11, ALLOC(dst));
}

static void isel_dtosi(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    if (instr.ret_t.t == TP_W) {
        EMIT2(CVTTSD2SI, L, ARG(v.t, v.a), R11D);
        EMIT2(MOV, L, R11D, ALLOC(dst));
    } else {
        EMIT2(CVTTSD2SI, Q, ARG(v.t, v.a), R11);
        EMIT2(MOV, Q, R11, ALLOC(dst));
    }
}

static void isel_dtoui(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    if (instr.ret_t.t == TP_W) {
        EMIT2(CVTTSD2SI, Q, ARG(v.t, v.a), R11);
    } else {
        EMIT2(MOVS, S, ARG(v.t, v.a), XMM8);
        EMIT2(CVTTSD2SI, Q, XMM8, R11);
        EMIT2(MOV, Q, R11, R10);
        EMIT2(SAR, Q, I64(63), R10);
        EMIT2(ADDS, S, F64(-9223372036854775808.0), XMM8);
        EMIT2(CVTTSD2SI, Q, XMM8, RAX);
        EMIT2(AND, Q, R10, RAX);
        EMIT2(OR, Q, RAX, R11);
    }
    EMIT2(MOV, Q, R11, ALLOC(dst));
}

static void isel_swtof(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    if (instr.ret_t.t == TP_S)
        EMIT2(CVTSI2S, S, ARG(v.t, v.a), XMM8);
    else
        EMIT2(CVTSI2S, D, ARG(v.t, v.a), XMM8);
    EMIT2(MOVS, D, XMM8, ALLOC(dst));
}

static void isel_uwtof(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10); /* R10 unused */
    if (instr.ret_t.t == TP_S) {
        EMIT2(MOV, L, ARG(v.t, v.a), R11D);
        EMIT2(CVTSI2S, S, R11, XMM8);
    } else {
        EMIT2(MOV, L, ARG(v.t, v.a), R11D);
        EMIT2(CVTSI2S, D, R11, XMM8);
    }
    EMIT2(MOVS, D, XMM8, ALLOC(dst));
}

static void isel_sltof(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10);
    if (instr.ret_t.t == TP_S)
        EMIT2(CVTSI2S, S, ARG(v.t, v.a), XMM8);
    else
        EMIT2(CVTSI2S, D, ARG(v.t, v.a), XMM8);
    EMIT2(MOVS, D, XMM8, ALLOC(dst));
}

static void isel_ultof(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10);
    EMIT2(MOV, Q, ARG(v.t, v.a), RAX);
    EMIT2(AND, Q, I64(1), RAX);
    EMIT2(MOV, Q, ARG(v.t, v.a), RDX);
    EMIT2(SHR, Q, I64(63), RDX);
    EMIT2(MOV, L, EDX, ECX);
    EMIT2(MOV, Q, ARG(v.t, v.a), RSI);
    EMIT2(SHR, Q, MREG(R_RCX, B), RSI);
    EMIT2(OR, Q, RSI, RAX);
    if (instr.ret_t.t == TP_S) {
        EMIT2(CVTSI2S, S, RAX, XMM8);
        EMIT2(MOV, Q, XMM8, RAX);
        EMIT2(MOV, L, EDX, ECX);
        EMIT2(SHL, L, I64(23), ECX);
        EMIT2(ADD, L, ECX, EAX);
    } else {
        EMIT2(CVTSI2S, D, RAX, XMM8);
        EMIT2(MOV, Q, XMM8, RAX);
        EMIT2(MOV, Q, RDX, RCX);
        EMIT2(SHL, Q, I64(52), RCX);
        EMIT2(ADD, Q, RCX, RAX);
    }
    EMIT2(MOV, Q, RAX, XMM8);
    EMIT2(MOVS, D, XMM8, ALLOC(dst));
}

static void isel_cast(Instr instr) {
    uint32_t dst = find_or_alloc_tmp(instr.ident);
    VisitValueResult v = visit_value(instr.u.args[0], R_R10);
    switch (instr.ret_t.t) {
    case TP_W: /* f32 => i32 */
        EMIT2(MOVS, S, ARG(v.t, v.a), XMM8);
        EMIT2(MOVQ, NONE, XMM8, ALLOC(dst));
        return;
    case TP_L: /* f64 => i64 */
        EMIT2(MOVS, D, ARG(v.t, v.a), XMM8);
        EMIT2(MOVQ, NONE, XMM8, ALLOC(dst));
        return;
    case TP_S: /* i32 => f32 */
        EMIT2(MOV, L, ARG(v.t, v.a), R11D);
        EMIT2(MOVQ, NONE, R11, XMM8);
        EMIT2(MOVS, D, XMM8, ALLOC(dst));
        return;
    case TP_D: /* i64 => f64 */
        EMIT2(MOV, Q, ARG(v.t, v.a), R11);
        EMIT2(MOVQ, NONE, R11, XMM8);
        EMIT2(MOVS, D, XMM8, ALLOC(dst));
        return;
    }
    fail("illegal cast op argument");
}

static void isel_copy(Instr instr) {
    VisitValueResult vvr = visit_value(instr.u.args[0], R_R10);
    if (instr.ret_t.t == TP_AG) {
        uint32_t tp_sz = Type_size(instr.ret_t);
        /* output of copy op */
        EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz),
              ALLOC(find_or_alloc_tmp(instr.ident)));
        /* actual coping */
        EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
        blit(MREG_OFF(R_R10, 0), ALLOC(asm_func.alloc_sz), tp_sz);
        asm_func.alloc_sz = (asm_func.alloc_sz + tp_sz + 7) & ~7;
    } else {
        uint32_t d = find_or_alloc_tmp(instr.ident);
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

/* returns amount of stack used for passing args.
   note that this also writes to RAX. */
static uint32_t prep_call_args(Instr instr, uint32_t ret_ag) {
    int i;
    uint32_t stk_arg_sz = 0;
    static uint8_t int_regs[] = {R_RDI, R_RSI, R_RDX, R_RCX, R_R8, R_R9};
    static uint8_t sse_regs[] = {
        R_XMM0, R_XMM1, R_XMM2, R_XMM3, R_XMM4, R_XMM5, R_XMM6, R_XMM7};
    uint8_t used_int_regs = 0, used_sse_regs = 0;

    /* if called func returns a large struct, provide output addr in %rdi, and
       let callee directly write into it.
       otherwise, manually copy return values after x64 call op. */
    if (instr.ret_t.t == TP_AG && Type_size(instr.ret_t) > 16) {
        EMIT2(LEA, Q, ALLOC(ret_ag), RDI);
        used_int_regs++;
    }

    for (i = 0; instr.u.call.args[i].t.t != TP_UNKNOWN; ++i) {
        VisitValueResult arg = visit_value(instr.u.call.args[i].v, R_R10);
        int use_stack = (used_int_regs == countof(int_regs) &&
                         used_sse_regs == countof(sse_regs));
        ClassifyResult cr = {0};
        uint32_t arg_sz;
        if (i == 0 && instr.u.call.args[i].t.t == TP_NONE) {
            /* QBE passes env using %rax,
               which is incompatible with varargs ABI. */
            EMIT2(MOV, Q, ARG(arg.t, arg.a), RAX);
            continue;
        } else {
            cr = classify(instr.u.call.args[i].t);
            arg_sz = Type_size(instr.u.call.args[i].t);
        }

        if (!use_stack) {
            use_stack = cr.fst == P_MEMORY;
            if (!use_stack) {
                uint8_t ir_cnt = 0, sr_cnt = 0;
                if (cr.fst == P_INTEGER) ir_cnt++;
                else if (cr.fst == P_SSE) sr_cnt++;
                if (cr.snd == P_INTEGER) ir_cnt++;
                else if (cr.snd == P_SSE) sr_cnt++;
                use_stack =
                    used_int_regs + ir_cnt > countof(int_regs) ||
                    used_sse_regs + sr_cnt > countof(sse_regs);
            }
        }

        if (!use_stack && instr.u.call.args[i].t.t == TP_AG) {
            /* use regs: aggregate type */
            int j;
            EMIT2(MOV, Q, ARG(arg.t, arg.a), R10);
            for (j = 0; j < 2; ++j) {
                if (((uint8_t *) &cr)[j] == P_INTEGER) {
                    EMIT2(MOV, Q, MREG_OFF(R_R10, 0), FAKE);
                    LAST_INSTR.arg[1].mreg.mreg = int_regs[used_int_regs++];
                } else if (((uint8_t *) &cr)[j] == P_SSE) {
                    EMIT2(MOVS, D, MREG_OFF(R_R10, 0), FAKE);
                    LAST_INSTR.arg[1].mreg.size = X64_SZ_D;
                    LAST_INSTR.arg[1].mreg.mreg = sse_regs[used_sse_regs++];
                }
            }
        } else if (!use_stack) {
            /* use regs: other types */
            switch (instr.u.call.args[i].t.t) {
            case TP_W:
                EMIT2(MOV, L, ARG(arg.t, arg.a), FAKE);
                LAST_INSTR.arg[1].mreg.size = X64_SZ_L;
                LAST_INSTR.arg[1].mreg.mreg = int_regs[used_int_regs++];
                break;
            case TP_L: case TP_NONE:
                EMIT2(MOV, Q, ARG(arg.t, arg.a), FAKE);
                LAST_INSTR.arg[1].mreg.size = X64_SZ_Q;
                LAST_INSTR.arg[1].mreg.mreg = int_regs[used_int_regs++];
                break;
            case TP_S:
                EMIT2(MOVS, S, ARG(arg.t, arg.a), FAKE);
                LAST_INSTR.arg[1].mreg.size = X64_SZ_S;
                LAST_INSTR.arg[1].mreg.mreg = sse_regs[used_sse_regs++];
                break;
            case TP_D:
                EMIT2(MOVS, D, ARG(arg.t, arg.a), FAKE);
                LAST_INSTR.arg[1].mreg.size = X64_SZ_D;
                LAST_INSTR.arg[1].mreg.mreg = sse_regs[used_sse_regs++];
                break;
            case TP_SB: case TP_UB:
                EMIT2(MOV, B, ARG(arg.t, arg.a), FAKE);
                LAST_INSTR.arg[1].mreg.size = X64_SZ_B;
                LAST_INSTR.arg[1].mreg.mreg = int_regs[used_int_regs++];
                break;
            case TP_SH: case TP_UH:
                EMIT2(MOV, W, ARG(arg.t, arg.a), FAKE);
                LAST_INSTR.arg[1].mreg.size = X64_SZ_W;
                LAST_INSTR.arg[1].mreg.mreg = int_regs[used_int_regs++];
                break;
            default:
                fail("unexpected argument TYPE");
                break; /* unreachable */
            }
        } else {
            /* use stack */
            switch (instr.u.call.args[i].t.t) {
#define SRC ARG(arg.t, arg.a)
#define DST STK_ARG(stk_arg_sz)
            case TP_W: EMIT2(MOV, L, SRC, DST); break;
            case TP_NONE:
            case TP_L: EMIT2(MOV, Q, SRC, DST); break;
            case TP_S: EMIT2(MOVS, S, SRC, DST); break;
            case TP_D: EMIT2(MOVS, D, SRC, DST); break;
            case TP_SB:
            case TP_UB: EMIT2(MOV, B, SRC, DST); break;
            case TP_SH:
            case TP_UH: EMIT2(MOV, W, SRC, DST); break;
            case TP_AG:
                EMIT2(MOV, Q, ARG(arg.t, arg.a), R10);
                blit(MREG_OFF(R_R10, 0), DST,
                     Type_size(instr.u.call.args[i].t));
                break;
#undef DST
#undef SRC
            default:
                fail("unexpected argument TYPE");
                break; /* unreachable */
            }

            if (instr.u.call.args[i].t.t == TP_AG) {
                stk_arg_sz += Type_size(instr.u.call.args[i].t);
                stk_arg_sz = (stk_arg_sz + 7) & ~7;
            } else {
                stk_arg_sz += 8;
            }
        }
    }

    if (instr.u.call.va_begin_idx <= i) {
        check(instr.u.call.args[0].t.t != TP_NONE,
              "env and varargs are incompatible on x64");
        EMIT2(MOV, B, I64(used_sse_regs), MREG(R_RAX, B));
    }

    return stk_arg_sz;
}

static void emit_call(Value f) {
    VisitValueResult vvr;
    switch (f.t) {
    case V_CSYM:
    case V_CTHS:
        EMIT1(CALL, Q, SYM(f.u.global_ident));
        return;
    case V_CI:
        EMIT2(MOV, Q, I64(f.u.u64), R10);
        EMIT1(CALL, Q, R10);
        return;
    case V_TMP:
        vvr = visit_value(f, R_R10);
        EMIT1(CALL, Q, ARG(vvr.t, vvr.a));
        return;
    default:
        fail("unexpected func VALUE type");
        break; /* unreachable */
    }
}

static void isel_call(Instr instr) {
    uint32_t stk_arg_sz = 0;
    uint32_t ret = 0, ret_ag = 0;
    ClassifyResult cr;
    int i;
    int used_int_regs = 0, used_sse_regs = 0;

    if (instr.ret_t.t != TP_NONE) {
        ret = find_or_alloc_tmp(instr.ident);
        if (instr.ret_t.t == TP_AG) {
            if (Type_log_align(instr.ret_t) == 4) /* align=16 */
                asm_func.alloc_sz = (asm_func.alloc_sz + 15) & ~15;
            ret_ag = asm_func.alloc_sz;
            asm_func.alloc_sz += Type_size(instr.ret_t);
            asm_func.alloc_sz = (asm_func.alloc_sz + 7) & ~7;
            EMIT2(LEA, Q, ALLOC(ret_ag), ALLOC(ret));
        }
    }

    EMIT2(SUB, Q, I64(0), RSP); /* for dynalloc */
    stk_arg_sz = prep_call_args(instr, ret_ag);
    emit_call(instr.u.call.f);
    EMIT2(ADD, Q, I64(0), RSP); /* for dynalloc */

    /* handle return value */
    if (instr.ret_t.t == TP_AG) {
        cr = classify(instr.ret_t);
        /* if cr.fst == P_MEMORY, nothing to be done here */
        for (i = 0; i < 2; ++i) {
            uint8_t *crp = (void *) &cr;
            if (crp[i] == P_SSE) {
                EMIT2(MOVS, D, FAKE, ALLOC(ret_ag + i * 8));
                LAST_INSTR.arg[0].mreg.mreg =
                    used_sse_regs == 0 ? R_XMM0 : R_XMM1;
                LAST_INSTR.arg[0].mreg.size = LAST_INSTR.size;
                used_sse_regs++;
            } else if (crp[i] == P_INTEGER) {
                EMIT2(MOV, Q, FAKE, ALLOC(ret_ag + i * 8));
                LAST_INSTR.arg[0].mreg.mreg =
                    used_int_regs == 0 ? R_RAX : R_RDX;
                used_int_regs++;
            }
        }
    } else {
        if (instr.ret_t.t == TP_S || instr.ret_t.t == TP_D)
            EMIT2(MOVS, D, XMM0, ALLOC(ret));
        else
            EMIT2(MOV, Q, RAX, ALLOC(ret));
    }

    if (stk_arg_sz > asm_func.stk_arg_sz)
        asm_func.stk_arg_sz = stk_arg_sz;
}

static void isel_vastart(Instr instr) {
    VisitValueResult p = visit_value(instr.u.args[0], R_R10);
    EMIT2(MOV, Q, ARG(p.t, p.a), R10);

    EMIT2(MOV, L, I64(ctx.gp_offset), MREG_OFF(R_R10, 0));
    EMIT2(MOV, L, I64(ctx.fp_offset), MREG_OFF(R_R10, 4));
    EMIT2(LEA, Q, PREV_STK_ARG(0), MREG_OFF(R_R10, 8));
    EMIT2(LEA, Q, ALLOC(ctx.reg_save_area), MREG_OFF(R_R10, 16));
}

static void isel_vaarg(Instr instr) {
    static uint32_t buf_suffix = 0;
    char buf[100];
    Ident else_label, end_label;

    uint32_t r = find_or_alloc_tmp(instr.ident);
    VisitValueResult vvr = visit_value(instr.u.args[0], R_R10);
    EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);

    sprintf(buf, "@wqbe_vaarg_%u", buf_suffix++);
    else_label = Ident_from_str(buf);
    sprintf(buf, "@wqbe_vaarg_%u", buf_suffix++);
    end_label = Ident_from_str(buf);

#define GP_OFFSET         MREG_OFF(R_R10,  0)
#define FP_OFFSET         MREG_OFF(R_R10,  4)
#define OVERFLOW_ARG_AREA MREG_OFF(R_R10,  8)
#define REG_SAVE_AREA     MREG_OFF(R_R10, 16)
    if (instr.ret_t.t == TP_S || instr.ret_t.t == TP_D) {
        EMIT2(CMP, L, I64(6 * 8 + 8 * 16), FP_OFFSET);
        EMIT1(JL, NONE, SYM(else_label));

        /* if fp_offset >= 6 * 8 + 8 * 16:
              *r = *overflow_arg_area;
              overflow_arg_area += 8; */
        EMIT2(MOV, Q, OVERFLOW_ARG_AREA, R11);
        if (instr.ret_t.t == TP_S)
            EMIT2(MOVS, S, MREG_OFF(R_R11, 0), ALLOC(r));
        else
            EMIT2(MOVS, D, MREG_OFF(R_R11, 0), ALLOC(r));
        EMIT2(ADD, Q, I64(8), OVERFLOW_ARG_AREA);
        EMIT1(JMP, NONE, SYM(end_label));

        /* else:
               *r = *(reg_save_area + fp_offset)
               fp_offset += 16; */
        emit_label(else_label);
        EMIT2(MOV, L, FP_OFFSET, R11D);
        EMIT2(ADD, Q, REG_SAVE_AREA, R11);
        if (instr.ret_t.t == TP_S)
            EMIT2(MOVS, S, MREG_OFF(R_R11, 0), ALLOC(r));
        else
            EMIT2(MOVS, D, MREG_OFF(R_R11, 0), ALLOC(r));
        EMIT2(ADD, L, I64(16), FP_OFFSET);

        emit_label(end_label);
    } else {
        check(instr.ret_t.t == TP_W || instr.ret_t.t == TP_L,
              "vaarg only supports wlsd");

        EMIT2(CMP, L, I64(6 * 8), GP_OFFSET);
        EMIT1(JL, NONE, SYM(else_label));

        /* if gp_offset >= 6 * 8:
               *r = *overflow_arg_area;
               overflow_arg_area += 8; */
        EMIT2(MOV, Q, OVERFLOW_ARG_AREA, R11);
        if (instr.ret_t.t == TP_W)
            EMIT2(MOV, L, MREG_OFF(R_R11, 0), ALLOC(r));
        else
            EMIT2(MOV, Q, MREG_OFF(R_R11, 0), ALLOC(r));
        EMIT2(ADD, Q, I64(8), OVERFLOW_ARG_AREA);
        EMIT1(JMP, NONE, SYM(end_label));

        /* else:
               *r = *(reg_save_area + gp_offset)
               gp_offset += 8; */
        emit_label(else_label);
        EMIT2(MOV, L, GP_OFFSET, R11D);
        EMIT2(ADD, Q, REG_SAVE_AREA, R11);
        if (instr.ret_t.t == TP_W)
            EMIT2(MOV, L, MREG_OFF(R_R11, 0), ALLOC(r));
        else
            EMIT2(MOV, Q, MREG_OFF(R_R11, 0), ALLOC(r));
        EMIT2(ADD, L, I64(8), GP_OFFSET);

        emit_label(end_label);
    }
#undef REG_SAVE_AREA
#undef OVERFLOW_ARG_AREA
#undef FP_OFFSET
#undef GP_OFFSET
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
    EMIT2(CMP, L, I64(0), ARG(vvr.t, vvr.a));
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
                /* RAX: required by ABI */
                EMIT2(MOV, Q, ALLOC(ctx.ret_ptr_alloc_offset), RAX);
                EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
                blit(MREG_OFF(R_R10, 0), MREG_OFF(R_RAX, 0), tp_sz);
            } else {
                int i;
                int used_int_regs = 0, used_sse_regs = 0;
                uint8_t *crp = (void*) &cr;
                EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);
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
    switch (instr.t) {
#define I(up,low) \
    case I_##up: isel_##low(instr); return;
#include "instr.inc"
#undef I
    }
    fail("unrecognized instr type %d", instr.t);
}

AsmFunc *isel_naive_x64(FuncDef *fd) {
    uint16_t blk_id;
    uint32_t instr_id;
    Block blk;
    Instr instr;

    memset(&asm_func, 0, sizeof(asm_func));
    memset(&ctx, 0, sizeof(ctx));
    ctx.fd = *fd;

    emit_prologue();

    blk_id = ctx.fd.blk_id;
    ctx.is_first_blk = 1;
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
        ctx.is_first_blk = 0;
    }

    /* ensure space for end marker (0) of instr and label */
    assert(ctx.instr_cnt < countof(asm_func.instr));
    assert(ctx.label_cnt < countof(asm_func.label));
    return &asm_func;
}
