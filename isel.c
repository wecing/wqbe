#include <assert.h>
#include <string.h>

#include "all.h"
#include "x64.h"

static AsmFunc asm_func;

static struct {
    FuncDef fd;
    uint32_t instr_cnt; /* AsmFunc.instr */
    uint32_t label_cnt; /* AsmFunc.label */
    int32_t ret_ptr_alloc_offset;

    struct {
        Ident ident;
        uint32_t id; /* > 0, vreg */
    } tmp[16 * 1024]; /* 16 * 8KB */
    uint8_t tmp_sz[16 * 1024]; /* 16 * 1KB; SZ_xxx */
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
    uint32_t overflow_arg_area; /* PREV_STK_ARG offset */
    uint32_t reg_save_area; /* ALLOC offset */
} ctx;

typedef struct VReg VReg;

static VReg find_or_alloc_tmp(Ident ident, uint8_t sz) {
    uint32_t i;
    VReg vreg;
    vreg.size = sz;
    for (i = 0; i < ctx.tmp_cnt; ++i)
        if (Ident_eq(ident, ctx.tmp[i].ident)) {
            vreg.id = ctx.tmp[i].id;
            return vreg;
        }
    assert(ctx.tmp_cnt < countof(ctx.tmp));
    ctx.tmp[ctx.tmp_cnt].ident = ident;
    ctx.tmp[ctx.tmp_cnt].id = ctx.tmp_cnt+1;
    ctx.tmp_sz[ctx.tmp_cnt] = sz;
    vreg.id = ctx.tmp_cnt+1;
    ctx.tmp_cnt++;
    return vreg;
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
#define SYM(id) AP_SYM, .sym=msym(id,AP_SYM_PLAIN,R_END,0)
#define SYM_OFF(id,off) AP_SYM, .sym=msym(id,AP_SYM_PLAIN,R_END,(off))
#define SYM_GOT(id) AP_SYM, .sym=msym(id,AP_SYM_GOTPCREL,R_END,0)
#define SYM_TPOFF(id,r) AP_SYM, .sym=msym(id,AP_SYM_TPOFF,(r),0)
#define MREG_OFF(r,off) AP_MREG, .mreg=mreg(X64_SZ_Q,(r),1,(off))
#define PREV_STK_ARG(off) MREG_OFF(R_RBP, 16+(off))
#define STK_ARG(off) MREG_OFF(R_RSP, (off))
#define VREG(r) AP_VREG, .vreg=(r)
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

static struct MSym msym(Ident ident, int t, int mreg, int offset) {
    struct MSym r;
    r.ident = ident;
    r.t = t;
    r.mreg = mreg;
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

/* ClassifyResult.(fst|snd) */
enum {
    P_NO_CLASS, /* ignored for passing */
    P_MEMORY,
    P_SSE,
    P_INTEGER
};
typedef struct ClassifyResult {
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

static void emit_reg_save(uint8_t used_int_regs, uint8_t used_sse_regs,
                          uint32_t used_stk_size) {
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
    ctx.overflow_arg_area = used_stk_size;
    ctx.reg_save_area = asm_func.alloc_sz;
    asm_func.alloc_sz += countof(int_regs) * 8 + countof(sse_regs) * 16;
    while (used_int_regs < countof(int_regs)) {
        EMIT2(MOV, Q, FAKE, ALLOC(ctx.reg_save_area + used_int_regs * 8));
        LAST_INSTR.arg[0].mreg.mreg = int_regs[used_int_regs];
        used_int_regs++;
    }
    w_snprintf(buf, sizeof(buf), "@wqbe_reg_save_end_%d", buf_suffix++);
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
    uint8_t ir_cnt, sr_cnt;
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
        uint32_t tp_sz, tp_align;
        uint8_t use_stack;
        VReg vreg;

        if (i == 0 && ctx.fd.params[i].t.t == TP_NONE) {
            /* env params are passed via %rax */
            vreg = find_or_alloc_tmp(ctx.fd.params[i].ident, X64_SZ_Q);
            EMIT2(MOV, Q, RAX, VREG(vreg));
            continue;
        }

        tp_sz = Type_size(ctx.fd.params[i].t);
        tp_align = 1u << Type_log_align(ctx.fd.params[i].t);

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

        /* aggregate: IR values are actually addresses */
        vreg = find_or_alloc_tmp(
            ctx.fd.params[i].ident,
            ctx.fd.params[i].t.t == TP_AG ? X64_SZ_Q : ctx.fd.params[i].t.t);

        if (!use_stack) { /* use regs */
            if (tp_align >= 16 && (asm_func.alloc_sz & (tp_align-1)))
                asm_func.alloc_sz =
                    (asm_func.alloc_sz + tp_align - 1) & ~(tp_align-1);
            if (ctx.fd.params[i].t.t == TP_AG) {
                EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz), VREG(vreg));
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
                switch (ctx.fd.params[i].t.t) {
                case TP_W:
                    EMIT2(MOV, L, FAKE, VREG(vreg));
                    break;
                case TP_L:
                    EMIT2(MOV, Q, FAKE, VREG(vreg));
                    break;
                case TP_SB:
                case TP_UB:
                    EMIT2(MOV, B, FAKE, VREG(vreg));
                    break;
                case TP_SH:
                case TP_UH:
                    EMIT2(MOV, W, FAKE, VREG(vreg));
                    break;
                case TP_S:
                    EMIT2(MOVS, S, FAKE, VREG(vreg));
                    break;
                case TP_D:
                    EMIT2(MOVS, D, FAKE, VREG(vreg));
                    break;
                default:
                    fail("unexpected FUNCDEF param type");
                }
                check(cr.fst == P_INTEGER || cr.fst == P_SSE,
                      "unexpected classify() result");
                if (cr.fst == P_INTEGER)
                    reg = int_regs[used_int_regs++];
                else
                    reg = sse_regs[used_sse_regs++];
                LAST_INSTR.arg[0].mreg.mreg = reg;
                LAST_INSTR.arg[0].mreg.size = LAST_INSTR.size;
            }
        } else { /* use stack */
            if (prev_stk_arg_size & (tp_align-1)) {
                /* copy to current frame to satisfy alignment needs */
                /* since prev_stk_arg_size is always 8-bytes aligned, this is
                   only occasionally needed for >=16 bytes alignments. */

                /* only aggregate types could trigger this */
                assert(ctx.fd.params[i].t.t == TP_AG);

                asm_func.alloc_sz =
                    (asm_func.alloc_sz + tp_align - 1) & ~(tp_align-1);
                EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz), VREG(vreg));

                blit(PREV_STK_ARG(prev_stk_arg_size), ALLOC(asm_func.alloc_sz),
                     tp_sz);

                prev_stk_arg_size = (prev_stk_arg_size + tp_sz + 7) & ~7;
                asm_func.alloc_sz = (asm_func.alloc_sz + tp_sz + 7) & ~7;
            } else if (ctx.fd.params[i].t.t == TP_AG) {
                EMIT2(LEA, Q, PREV_STK_ARG(prev_stk_arg_size), VREG(vreg));
                prev_stk_arg_size = (prev_stk_arg_size + tp_sz + 7) & ~7;
            } else {
                check(cr.fst == P_INTEGER || cr.fst == P_SSE,
                      "unexpected classify() result");
                if (cr.fst == P_INTEGER)
                    EMIT2(MOV, Q, PREV_STK_ARG(prev_stk_arg_size), VREG(vreg));
                else
                    EMIT2(MOVS, D, PREV_STK_ARG(prev_stk_arg_size), VREG(vreg));
                prev_stk_arg_size = (prev_stk_arg_size + tp_sz + 7) & ~7;
            }
        }
    }

    emit_reg_save(used_int_regs, used_sse_regs, prev_stk_arg_size);
}

#define isel_alloc16 isel_alloc
#define isel_alloc4  isel_alloc
#define isel_alloc8  isel_alloc

static void isel_alloc(Instr instr) {
    (void)instr;
    fail("not implemented");
}

static void isel_cnel(Instr instr) {
    (void)instr;
    fail("not implemented");
}

static void isel(Instr instr) {
    switch (instr.t) {
    case I_ALLOC8: isel_alloc8(instr); return;
    case I_CNEL: isel_cnel(instr); return;
    }
    fail("unrecognized instr type %d", instr.t);
}

AsmFunc *isel_x64(FuncDef *fd) {
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
