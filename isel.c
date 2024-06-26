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
            if (sz == X64_SZ_NONE)
                vreg.size = ctx.tmp_sz[i];
            return vreg;
        }
    assert(ctx.tmp_cnt < countof(ctx.tmp));
    check(sz != X64_SZ_NONE, "use before define of TMP detected");
    ctx.tmp[ctx.tmp_cnt].ident = ident;
    ctx.tmp[ctx.tmp_cnt].id = ctx.tmp_cnt+1;
    ctx.tmp_sz[ctx.tmp_cnt] = sz;
    vreg.id = ctx.tmp_cnt+1;
    ctx.tmp_cnt++;
    return vreg;
}

uint8_t get_vreg_sz(Type t) {
    switch (t.t) {
    case TP_W: return X64_SZ_L;
    case TP_L: return X64_SZ_Q;
    case TP_S: return X64_SZ_S;
    case TP_D: return X64_SZ_D;
    default:
        fail("get_vreg_sz: unsupported type.t: %d", t.t);
        return 0; /* unreachable */
    }
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
#define XMM1 MREG(R_XMM1,D)
#define XMM15 MREG(R_XMM15,D)
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
    int blk_id = ctx.fd.blk_id;
    Block blk;
    char buf[100];
    Ident skip_label;
    static int buf_suffix = 0;

    while (blk_id) {
        Instr *p;
        blk = *Block_get(blk_id);
        blk_id = blk.next_id;
        for (p = blk.dummy_head->next; p != blk.dummy_tail; p = p->next)
            if (p->t == I_VASTART)
                goto proceed;
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
#ifdef __OpenBSD__
    EMIT0(ENDBR64, NONE);
#endif
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
            ctx.fd.params[i].t.t == TP_AG
            ? X64_SZ_Q
            : get_vreg_sz(ctx.fd.params[i].t));

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
                if (cr.fst == P_INTEGER) {
                    vreg.size = X64_SZ_Q;
                    EMIT2(MOV, Q, PREV_STK_ARG(prev_stk_arg_size), VREG(vreg));
                } else {
                    vreg.size = X64_SZ_D;
                    EMIT2(MOVS, D, PREV_STK_ARG(prev_stk_arg_size), VREG(vreg));
                }
                prev_stk_arg_size = (prev_stk_arg_size + tp_sz + 7) & ~7;
            }
        }
    }

    emit_reg_save(used_int_regs, used_sse_regs, prev_stk_arg_size);
}

typedef struct VisitValueResult {
    uint8_t t; /* AP_xxx */
    AsmInstrArg a;
} VisitValueResult;

static Ident visit_value_unique_ident(void) {
    static int last_id = 0;
    char buf[25];
    w_snprintf(buf, sizeof(buf), ".wqbe.vvr.%d", ++last_id);
    return Ident_from_str(buf);
}

static VisitValueResult
visit_value_impl(Value v, uint8_t vreg_sz, uint8_t tmp_mreg) {
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
        r.t = AP_VREG;
        r.a.vreg = find_or_alloc_tmp(visit_value_unique_ident(), X64_SZ_Q);
        EMIT2(LEA, Q, SYM(v.u.global_ident), MREG(tmp_mreg, Q));
        EMIT2(MOV, Q, MREG(tmp_mreg, Q), VREG(r.a.vreg));
        return r;
    case V_CTHS:
        r.t = AP_VREG;
        r.a.vreg = find_or_alloc_tmp(visit_value_unique_ident(), X64_SZ_Q);
        EMIT2(MOV, Q, I64(0), MREG(tmp_mreg, Q));
        LAST_INSTR.arg0_use_fs = 1;
        EMIT2(LEA, Q, SYM_TPOFF(v.u.thread_ident, tmp_mreg), VREG(r.a.vreg));
        return r;
    case V_TMP:
        /* prohibit visiting usage before def */
        r.t = AP_VREG;
        r.a.vreg = find_or_alloc_tmp(v.u.tmp_ident, vreg_sz);
        return r;
    default: break;
    }
    fail("unrecognized VALUE type");
    return r; /* unreachable */
}

/* NOTE: %rax should not be pre-colored and alive on calling this
   (using %rax so it's more likely to be reused by reg alloc) */
static VisitValueResult
visit_value(Value v, uint8_t vreg_sz) {
    return visit_value_impl(v, vreg_sz, R_RAX);
}

/* avoid expressions like `divl $42`; introduces a new vreg for the imm.
   no need to handle imm64/fp since they will be converted to mem in ra_naive */
static VisitValueResult
visit_value_avoid_imm32(VisitValueResult v, uint8_t vreg_sz) {
    if (v.t == AP_I64 && !(v.a.i64 & ~0x7FFFFFFFL)) {
        VisitValueResult r;
        r.t = AP_VREG;
        r.a.vreg = find_or_alloc_tmp(visit_value_unique_ident(), vreg_sz);
        EMIT2(MOV, NONE, I64(v.a.i64), VREG(r.a.vreg));
        LAST_INSTR.size = vreg_sz;
        /* fp constant written as i64 literal */
        if (vreg_sz == X64_SZ_S || vreg_sz == X64_SZ_D)
            LAST_INSTR.t = A_MOVS;
        return r;
    }
    return v;
}

/* QBE has test cases like this:

       %a =w add %pf1, %a

   in practice we should always run SSA construction algorithm before reaching
   here, so that pattern is impossible. but, QBE has that test case, and we want
   to make our impl correct even without SSA construction, so we need to be
   careful not to overwrite output too early in mid-computation.

   that is to say, we cannot emit assembly like:

       movq left, out
       addq right, out

   instead, we do:

       movq left, %r11
       addq right, %r11
       movq %r11, out

   (that pattern is required for IMUL anyways, since it cannot output to mem.)
*/

static Ident arith_new_tmp(void) {
    static int n = 0;
    char buf[30];
    w_snprintf(buf, sizeof(buf), ".wqbe.arith.%d", n++);
    return Ident_from_str(buf);
}

#define arith_wlsd(op,ixop,fxop) \
    static void isel_##op(Instr instr) { \
        uint8_t vreg_sz = get_vreg_sz(instr.ret_t); \
        VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz); \
        VReg tmp = find_or_alloc_tmp(arith_new_tmp(), vreg_sz); \
        VisitValueResult x = visit_value(instr.u.args[0], vreg_sz); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), VREG(tmp)); \
            x = visit_value(instr.u.args[1], vreg_sz); \
            EMIT2(ixop, L, ARG(x.t, x.a), VREG(tmp)); \
            EMIT2(MOV, L, VREG(tmp), VREG(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), VREG(tmp)); \
            x = visit_value(instr.u.args[1], vreg_sz); \
            EMIT2(ixop, Q, ARG(x.t, x.a), VREG(tmp)); \
            EMIT2(MOV, Q, VREG(tmp), VREG(dst)); \
        } else if (instr.ret_t.t == TP_S) { \
            EMIT2(MOVS, S, ARG(x.t, x.a), VREG(tmp)); \
            x = visit_value(instr.u.args[1], vreg_sz); \
            EMIT2(fxop, S, ARG(x.t, x.a), VREG(tmp)); \
            EMIT2(MOVS, S, VREG(tmp), VREG(dst)); \
        } else if (instr.ret_t.t == TP_D) { \
            EMIT2(MOVS, D, ARG(x.t, x.a), VREG(tmp)); \
            x = visit_value(instr.u.args[1], vreg_sz); \
            EMIT2(fxop, D, ARG(x.t, x.a), VREG(tmp)); \
            EMIT2(MOVS, D, VREG(tmp), VREG(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

#define arith_wl(op,xop) \
    static void isel_##op(Instr instr) { \
        uint8_t vreg_sz = get_vreg_sz(instr.ret_t); \
        VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz); \
        VReg tmp = find_or_alloc_tmp(arith_new_tmp(), vreg_sz); \
        VisitValueResult x = visit_value(instr.u.args[0], vreg_sz); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), VREG(tmp)); \
            x = visit_value(instr.u.args[1], vreg_sz); \
            EMIT2(xop, L, ARG(x.t, x.a), VREG(tmp)); \
            EMIT2(MOV, L, VREG(tmp), VREG(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), VREG(tmp)); \
            x = visit_value(instr.u.args[1], vreg_sz); \
            EMIT2(xop, Q, ARG(x.t, x.a), VREG(tmp)); \
            EMIT2(MOV, Q, VREG(tmp), VREG(dst)); \
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
    uint8_t vreg_sz = get_vreg_sz(instr.ret_t);
    VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz);
    VisitValueResult y = visit_value(instr.u.args[1], vreg_sz);
    VisitValueResult x = visit_value(instr.u.args[0], vreg_sz);
    y = visit_value_avoid_imm32(y, vreg_sz);
    if (instr.ret_t.t == TP_W) {
        EMIT2(MOV, L, ARG(x.t, x.a), EAX);
        EMIT0(CLTD, NONE);
        EMIT1(IDIV, L, ARG(y.t, y.a));
        EMIT2(MOV, L, EAX, VREG(dst));
    } else if (instr.ret_t.t == TP_L) {
        EMIT2(MOV, Q, ARG(x.t, x.a), RAX);
        EMIT0(CQTO, NONE);
        EMIT1(IDIV, Q, ARG(y.t, y.a));
        EMIT2(MOV, Q, RAX, VREG(dst));
    } else if (instr.ret_t.t == TP_S) {
        EMIT2(MOVS, S, ARG(x.t, x.a), VREG(dst));
        EMIT2(DIVS, S, ARG(y.t, y.a), VREG(dst));
    } else if (instr.ret_t.t == TP_D) {
        EMIT2(MOVS, D, ARG(x.t, x.a), VREG(dst));
        EMIT2(DIVS, D, ARG(y.t, y.a), VREG(dst));
    } else {
        fail("unexpected return type");
    }
}

#define int_div_rem(op,xop,r) \
    static void isel_##op(Instr instr) { \
        uint8_t vreg_sz = get_vreg_sz(instr.ret_t); \
        VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz); \
        VisitValueResult y = visit_value(instr.u.args[1], vreg_sz); \
        VisitValueResult x = visit_value(instr.u.args[0], vreg_sz); \
        y = visit_value_avoid_imm32(y, vreg_sz); \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), EAX); \
            if (A_##xop == A_IDIV) \
                EMIT0(CLTD, NONE); \
            else \
                EMIT2(MOV, Q, I64(0), RDX); \
            EMIT1(xop, L, ARG(y.t, y.a)); \
            EMIT2(MOV, L, MREG(r, L), VREG(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), RAX); \
            if (A_##xop == A_IDIV) \
                EMIT0(CQTO, NONE); \
            else \
                EMIT2(MOV, Q, I64(0), RDX); \
            EMIT1(xop, Q, ARG(y.t, y.a)); \
            EMIT2(MOV, Q, MREG(r, Q), VREG(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

int_div_rem(udiv,DIV,R_RAX)
int_div_rem(rem,IDIV,R_RDX)
int_div_rem(urem,DIV,R_RDX)

#define shift_wl(op,xop) \
    static void isel_##op(Instr instr) { \
        uint8_t vreg_sz = get_vreg_sz(instr.ret_t); \
        VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz); \
        VisitValueResult x = visit_value(instr.u.args[0], vreg_sz); \
        VisitValueResult y = visit_value(instr.u.args[1], X64_SZ_L); \
        /* sar/shl/shr %cl, r/m */ \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(MOV, L, ARG(x.t, x.a), VREG(dst)); \
            EMIT2(MOV, L, ARG(y.t, y.a), MREG(R_RCX, L)); \
            EMIT2(xop, L, MREG(R_RCX, B), VREG(dst)); \
        } else if (instr.ret_t.t == TP_L) { \
            EMIT2(MOV, Q, ARG(x.t, x.a), VREG(dst)); \
            EMIT2(MOV, L, ARG(y.t, y.a), MREG(R_RCX, L)); \
            EMIT2(xop, Q, MREG(R_RCX, B), VREG(dst)); \
        } else { \
            fail("unexpected return type"); \
        } \
    }

shift_wl(sar, SAR)
shift_wl(shl, SHL)
shift_wl(shr, SHR)

static void isel_neg(Instr instr) {
    uint8_t vreg_sz = get_vreg_sz(instr.ret_t);
    VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz);
    VisitValueResult vvr = visit_value(instr.u.args[0], vreg_sz);
    if (instr.ret_t.t == TP_W) {
        EMIT2(MOV, L, ARG(vvr.t, vvr.a), VREG(dst));
        EMIT1(NEG, L, VREG(dst));
    } else if (instr.ret_t.t == TP_L) {
        EMIT2(MOV, Q, ARG(vvr.t, vvr.a), VREG(dst));
        EMIT1(NEG, Q, VREG(dst));
    } else if (instr.ret_t.t == TP_S) {
        EMIT2(MOVQ, NONE, ARG(vvr.t, vvr.a), R11);
        EMIT2(XOR, L, I64(1L << 31), R11D);
        EMIT2(MOV, L, R11D, R11D);
        EMIT2(MOVQ, NONE, R11, VREG(dst));
    } else if (instr.ret_t.t == TP_D) {
        EMIT2(MOVQ, NONE, ARG(vvr.t, vvr.a), R11);
        EMIT2(XOR, Q, I64(1L << 63), R11);
        EMIT2(MOV, Q, R11, VREG(dst));
    } else {
        fail("unexpected return type");
    }
}

#define isel_alloc16 isel_alloc
#define isel_alloc4  isel_alloc
#define isel_alloc8  isel_alloc

static void isel_alloc(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, X64_SZ_Q);
    if (ctx.is_first_blk && instr.u.args[0].t == V_CI) {
        uint32_t sz = (instr.u.args[0].u.u64 + 7) & ~7;
        if (instr.t == I_ALLOC16)
            asm_func.alloc_sz = (asm_func.alloc_sz + 15) & ~15;
        EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz), VREG(dst));
        asm_func.alloc_sz += sz;
    } else {
        asm_func.has_dyn_alloc = 1;
        if (instr.u.args[0].t == V_CI) {
            uint32_t sz = (instr.u.args[0].u.u64 + 7) & ~7;
            if (instr.t == I_ALLOC16)
                sz += 8;
            if (sz > 0) /* avoid subq $0, %rsp, which has special meaning */
                EMIT2(SUB, Q, I64(sz), RSP);
        } else {
            VisitValueResult vvr = visit_value(instr.u.args[0], X64_SZ_L);
            EMIT2(MOV, Q, ARG(vvr.t, vvr.a), RAX);
            EMIT2(ADD, Q, I64(7), RAX);
            EMIT2(AND, Q, I64(~7), RAX);
            if (instr.t == I_ALLOC16)
                EMIT2(ADD, Q, I64(8), RAX);
            EMIT2(SUB, Q, RAX, RSP);
        }
        EMIT2(MOV, Q, RSP, VREG(dst));
        if (instr.t == I_ALLOC16) {
            EMIT2(ADD, Q, I64(15), VREG(dst));
            EMIT2(AND, Q, I64(~15), VREG(dst));
        }
    }
}

static void isel_blit(Instr instr) {
    VisitValueResult src = visit_value(instr.u.args[0], X64_SZ_Q);
    VisitValueResult dst = visit_value(instr.u.args[1], X64_SZ_Q);
    EMIT2(MOV, Q, ARG(src.t, src.a), RDI);
    EMIT2(MOV, Q, ARG(dst.t, dst.a), RAX);
    blit(MREG_OFF(R_RDI, 0), MREG_OFF(R_RAX, 0), instr.blit_sz);
}

static void isel_load(Instr instr) {
    (void) instr;
    fail("unexpected LOAD instruction"); /* parser shouldn't output this */
}

#define load_mem_simple(op,mv,xs) \
    static void isel_##op(Instr instr) { \
        VReg dst = find_or_alloc_tmp(instr.ident, X64_SZ_##xs); \
        VisitValueResult p = visit_value(instr.u.args[0], X64_SZ_Q); \
        EMIT2(MOV, Q, ARG(p.t, p.a), RAX); \
        EMIT2(mv, xs, MREG_OFF(R_RAX, 0), VREG(dst)); \
    }

load_mem_simple(loadl,  MOV, Q)
load_mem_simple(loads, MOVS, S)
load_mem_simple(loadd, MOVS, D)

#define load_mem_bhw(op,xqop,xqsz,xlop,xlsz) \
    static void isel_##op(Instr instr) { \
        uint8_t vreg_sz = get_vreg_sz(instr.ret_t); \
        VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz); \
        VisitValueResult p = visit_value(instr.u.args[0], X64_SZ_Q); \
        EMIT2(MOV, Q, ARG(p.t, p.a), RAX); \
        if (instr.ret_t.t == TP_L) { \
            EMIT2(xqop, xqsz, MREG_OFF(R_RAX, 0), MREG(R_RAX, xqsz)); \
            EMIT2(MOV, Q, MREG(R_RAX, Q), VREG(dst)); \
        } else { \
            EMIT2(xlop, xlsz, MREG_OFF(R_RAX, 0), MREG(R_RAX, xlsz)); \
            EMIT2(MOV, L, MREG(R_RAX, L), VREG(dst)); \
        } \
    }

load_mem_bhw(loadsw, MOVSL, Q, MOV,   L)
load_mem_bhw(loaduw, MOV,   L, MOV,   L)
load_mem_bhw(loadsh, MOVSW, Q, MOVSW, L)
load_mem_bhw(loaduh, MOVZW, Q, MOVZW, L)
load_mem_bhw(loadsb, MOVSB, Q, MOVSB, L)
load_mem_bhw(loadub, MOVZB, Q, MOVZB, L)

#define isel_loadw isel_loadsw

#define store_mem(op,mv,xs,tmp) \
    static void isel_##op(Instr instr) { \
        uint8_t vreg_sz = \
            X64_SZ_##xs == X64_SZ_Q ? X64_SZ_Q \
            : X64_SZ_##xs == X64_SZ_S ? X64_SZ_S \
            : X64_SZ_##xs == X64_SZ_D ? X64_SZ_D \
            : X64_SZ_L; \
        VisitValueResult v = visit_value(instr.u.args[0], vreg_sz); \
        VisitValueResult p = visit_value(instr.u.args[1], X64_SZ_Q); \
        if (X64_SZ_##xs == X64_SZ_Q) { \
            EMIT2(MOV, Q, ARG(p.t, p.a), RAX); \
            EMIT2(MOV, Q, ARG(v.t, v.a), MREG_OFF(R_RAX, 0)); \
        } else { \
            if (X64_SZ_##xs == X64_SZ_B) { \
                if (v.t == AP_MREG) { \
                    v.a.mreg.size = X64_SZ_B; \
                } else if (v.t == AP_VREG) { \
                    v.a.vreg.size = X64_SZ_B; \
                } \
            } else if (X64_SZ_##xs == X64_SZ_W) { \
                if (v.t == AP_MREG) { \
                    v.a.mreg.size = X64_SZ_W; \
                } else if (v.t == AP_VREG) { \
                    v.a.vreg.size = X64_SZ_W; \
                } \
            } \
            EMIT2(mv, xs, ARG(v.t, v.a), MREG(tmp, xs)); \
            EMIT2(MOV, Q, ARG(p.t, p.a), RAX); \
            EMIT2(mv, xs, MREG(tmp, xs), MREG_OFF(R_RAX, 0)); \
        } \
    }

store_mem(storeb,  MOV, B, R_RDI)
store_mem(storeh,  MOV, W, R_RDI)
store_mem(storew,  MOV, L, R_RDI)
store_mem(storel,  MOV, Q, R_RDI)
store_mem(stores, MOVS, S, R_XMM0)
store_mem(stored, MOVS, D, R_XMM0)

#define cmp_int_impl(op,s,xs,xop) \
    static void isel_c##op##s(Instr instr) { \
        VReg dst = find_or_alloc_tmp( \
            instr.ident, instr.ret_t.t == TP_W ? X64_SZ_L : X64_SZ_Q); \
        VisitValueResult x = visit_value(instr.u.args[0], X64_SZ_##xs); \
        VisitValueResult y = visit_value(instr.u.args[1], X64_SZ_##xs); \
        x = visit_value_avoid_imm32(x, X64_SZ_##xs); \
        if (instr.ret_t.t == TP_W) \
            EMIT2(MOV, L, I64(0), VREG(dst)); \
        else \
            EMIT2(MOV, Q, I64(0), VREG(dst)); \
        dst.size = X64_SZ_B; \
        EMIT2(CMP, xs, ARG(y.t, y.a), ARG(x.t, x.a)); \
        EMIT1(xop, NONE, VREG(dst)); \
    }
#define cmp_int(op,xop) \
    cmp_int_impl(op,w,L,xop) \
    cmp_int_impl(op,l,Q,xop)

/* eq/ne for fp needs special treatment.
   (ucomisd NaN, NaN) sets ZF=1 but (NaN cmp NaN) is false. */

static void isel_clts(Instr);
static void isel_cltd(Instr);
static void isel_cles(Instr);
static void isel_cled(Instr);

#define cmp_sse_impl(op,s,xs,xop) \
    static void isel_c##op##s(Instr instr) { \
        VReg dst = find_or_alloc_tmp( \
            instr.ident, instr.ret_t.t == TP_W ? X64_SZ_L : X64_SZ_Q); \
        VisitValueResult x = visit_value(instr.u.args[0], X64_SZ_##xs); \
        VisitValueResult y = visit_value(instr.u.args[1], X64_SZ_##xs); \
        if (instr.ret_t.t == TP_W) \
            EMIT2(MOV, L, I64(0), VREG(dst)); \
        else \
            EMIT2(MOV, Q, I64(0), VREG(dst)); \
        dst.size = X64_SZ_B; \
        if (A_##xop == A_SETE || A_##xop == A_SETNE) \
            EMIT2(MOV, Q, I64(0), MREG(R_R11,Q)); \
        if (isel_c##op##s == isel_clts || isel_c##op##s == isel_cles || \
            isel_c##op##s == isel_cltd || isel_c##op##s == isel_cled) { \
            EMIT2(UCOMIS, xs, ARG(x.t, x.a), ARG(y.t, y.a)); \
        } else { \
            EMIT2(UCOMIS, xs, ARG(y.t, y.a), ARG(x.t, x.a)); \
        } \
        EMIT1(xop, NONE, VREG(dst)); \
        if (A_##xop == A_SETE) { \
            EMIT1(SETNP, NONE, MREG(R_R11,B)); \
            EMIT2(AND, B, MREG(R_R11,B), VREG(dst)); \
        } else if (A_##xop == A_SETNE) { \
            EMIT1(SETP, NONE, MREG(R_R11,B)); \
            EMIT2(OR, B, MREG(R_R11,B), VREG(dst)); \
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
cmp_sse(le, SETAE) /* swap operands for NaN */
cmp_sse(lt, SETA) /* swap operands for NaN */
cmp_sse(ge, SETAE)
cmp_sse(gt, SETA)
cmp_sse(o, SETNP)
cmp_sse(uo, SETP)

static void isel_truncd(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, X64_SZ_S);
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_D);
    EMIT2(CVTSD2S, S, ARG(v.t, v.a), VREG(dst));
}

static void isel_exts(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, X64_SZ_D);
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_S);
    EMIT2(CVTSS2S, D, ARG(v.t, v.a), VREG(dst));
}

static void isel_extsw(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, X64_SZ_Q);
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_L);
    v = visit_value_avoid_imm32(v, X64_SZ_L);
    EMIT2(MOVSL, Q, ARG(v.t, v.a), VREG(dst));
}

static void isel_extuw(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, X64_SZ_Q);
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_L);
    EMIT2(MOV, L, ARG(v.t, v.a), R11D);
    EMIT2(MOV, Q, R11, VREG(dst));
}

#define ext_hb(op,xop,sz) \
    static void isel_##op(Instr instr) { \
        VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t)); \
        VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_L); \
        v = visit_value_avoid_imm32(v, X64_SZ_L); \
        if (v.t == AP_VREG) \
            v.a.vreg.size = X64_SZ_##sz; \
        if (instr.ret_t.t == TP_W) { \
            EMIT2(xop, L, ARG(v.t, v.a), VREG(dst)); \
        } else { \
            EMIT2(xop, Q, ARG(v.t, v.a), VREG(dst)); \
        } \
    }

ext_hb(extsh, MOVSW, W)
ext_hb(extuh, MOVZW, W)
ext_hb(extsb, MOVSB, B)
ext_hb(extub, MOVZB, B)

static void isel_stosi(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_S);
    if (instr.ret_t.t == TP_W) {
        EMIT2(CVTTSS2SI, L, ARG(v.t, v.a), VREG(dst));
    } else {
        EMIT2(CVTTSS2SI, Q, ARG(v.t, v.a), VREG(dst));
    }
}

static void isel_stoui(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_S);
    if (instr.ret_t.t == TP_W) {
        dst.size = X64_SZ_Q;
        EMIT2(CVTTSS2SI, Q, ARG(v.t, v.a), VREG(dst));
    } else {
        EMIT2(MOVS, S, ARG(v.t, v.a), XMM15);
        EMIT2(CVTTSS2SI, Q, XMM15, VREG(dst));
        EMIT2(MOV, Q, VREG(dst), R10);
        EMIT2(SAR, Q, I64(63), R10);
        EMIT2(ADDS, S, F32(-9223372036854775808.0), XMM15);
        EMIT2(CVTTSS2SI, Q, XMM15, R11);
        EMIT2(AND, Q, R10, R11);
        EMIT2(OR, Q, R11, VREG(dst));
    }
}

static void isel_dtosi(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_D);
    if (instr.ret_t.t == TP_W) {
        EMIT2(CVTTSD2SI, L, ARG(v.t, v.a), VREG(dst));
    } else {
        EMIT2(CVTTSD2SI, Q, ARG(v.t, v.a), VREG(dst));
    }
}

static void isel_dtoui(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_D);
    if (instr.ret_t.t == TP_W) {
        dst.size = X64_SZ_Q;
        EMIT2(CVTTSD2SI, Q, ARG(v.t, v.a), VREG(dst));
    } else {
        EMIT2(MOVS, D, ARG(v.t, v.a), XMM15);
        EMIT2(CVTTSD2SI, Q, XMM15, VREG(dst));
        EMIT2(MOV, Q, VREG(dst), R10);
        EMIT2(SAR, Q, I64(63), R10);
        EMIT2(ADDS, D, F64(-9223372036854775808.0), XMM15);
        EMIT2(CVTTSD2SI, Q, XMM15, R11);
        EMIT2(AND, Q, R10, R11);
        EMIT2(OR, Q, R11, VREG(dst));
    }
}

static void isel_swtof(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_L);
    if (instr.ret_t.t == TP_S)
        EMIT2(CVTSI2SS, L, ARG(v.t, v.a), VREG(dst));
    else
        EMIT2(CVTSI2SD, L, ARG(v.t, v.a), VREG(dst));
}

static void isel_uwtof(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_L);
    EMIT2(MOV, L, ARG(v.t, v.a), R11D);
    if (instr.ret_t.t == TP_S) {
        EMIT2(CVTSI2SS, Q, R11, VREG(dst));
    } else {
        EMIT2(CVTSI2SD, Q, R11, VREG(dst));
    }
}

static void isel_sltof(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_Q);
    if (instr.ret_t.t == TP_S)
        EMIT2(CVTSI2SS, Q, ARG(v.t, v.a), VREG(dst));
    else
        EMIT2(CVTSI2SD, Q, ARG(v.t, v.a), VREG(dst));
}

static void isel_ultof(Instr instr) {
    VReg dst = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult v = visit_value(instr.u.args[0], X64_SZ_Q);
    EMIT2(MOV, Q, ARG(v.t, v.a), RAX);
    EMIT2(AND, Q, I64(1), RAX);
    EMIT2(MOV, Q, ARG(v.t, v.a), RDX);
    EMIT2(SHR, Q, I64(63), RDX);
    EMIT2(MOV, L, EDX, ECX);
    EMIT2(MOV, Q, ARG(v.t, v.a), RSI);
    EMIT2(SHR, Q, MREG(R_RCX, B), RSI);
    EMIT2(OR, Q, RSI, RAX);
    if (instr.ret_t.t == TP_S) {
        EMIT2(CVTSI2SS, Q, RAX, XMM15);
        EMIT2(MOV, Q, XMM15, RAX);
        EMIT2(MOV, L, EDX, ECX);
        EMIT2(SHL, L, I64(23), ECX);
        EMIT2(ADD, L, ECX, EAX);
    } else {
        EMIT2(CVTSI2SD, Q, RAX, XMM15);
        EMIT2(MOV, Q, XMM15, RAX);
        EMIT2(MOV, Q, RDX, RCX);
        EMIT2(SHL, Q, I64(52), RCX);
        EMIT2(ADD, Q, RCX, RAX);
    }
    EMIT2(MOV, Q, RAX, XMM15);
    EMIT2(MOVS, D, XMM15, VREG(dst));
}

static void isel_cast(Instr instr) {
    uint8_t vreg_sz = get_vreg_sz(instr.ret_t);
    VReg dst = find_or_alloc_tmp(instr.ident, vreg_sz);
    VisitValueResult v;
    switch (instr.ret_t.t) {
    case TP_W: /* f32 => i32 */
        v = visit_value(instr.u.args[0], X64_SZ_S);
        EMIT2(MOVS, S, ARG(v.t, v.a), XMM15);
        dst.size = X64_SZ_Q; /* movq xmm, r/m64 */
        EMIT2(MOVQ, NONE, XMM15, VREG(dst));
        return;
    case TP_L: /* f64 => i64 */
        v = visit_value(instr.u.args[0], X64_SZ_D);
        EMIT2(MOVS, D, ARG(v.t, v.a), XMM15);
        EMIT2(MOVQ, NONE, XMM15, VREG(dst));
        return;
    case TP_S: /* i32 => f32 */
        v = visit_value(instr.u.args[0], X64_SZ_L);
        EMIT2(MOV, L, ARG(v.t, v.a), EAX);
        EMIT2(MOVQ, NONE, RAX, XMM15);
        EMIT2(MOVS, D, XMM15, VREG(dst));
        return;
    case TP_D: /* i64 => f64 */
        v = visit_value(instr.u.args[0], X64_SZ_Q);
        EMIT2(MOV, Q, ARG(v.t, v.a), RAX);
        EMIT2(MOVQ, NONE, RAX, XMM15);
        EMIT2(MOVS, D, XMM15, VREG(dst));
        return;
    }
    fail("illegal cast op argument");
}

static void isel_copy(Instr instr) {
    uint8_t vreg_sz =
        instr.ret_t.t == TP_AG ? X64_SZ_Q : get_vreg_sz(instr.ret_t);
    VisitValueResult vvr = visit_value(instr.u.args[0], vreg_sz);
    if (instr.ret_t.t == TP_AG) {
        uint32_t tp_sz = Type_size(instr.ret_t);
        /* output of copy op */
        EMIT2(LEA, Q, ALLOC(asm_func.alloc_sz),
              VREG(find_or_alloc_tmp(instr.ident, X64_SZ_Q)));
        /* actual coping */
        EMIT2(MOV, Q, ARG(vvr.t, vvr.a), RAX);
        blit(MREG_OFF(R_RAX, 0), ALLOC(asm_func.alloc_sz), tp_sz);
        asm_func.alloc_sz = (asm_func.alloc_sz + tp_sz + 7) & ~7;
    } else {
        VReg d = find_or_alloc_tmp(instr.ident, vreg_sz);
        switch (instr.ret_t.t) {
        case TP_W: EMIT2(MOV, L, ARG(vvr.t, vvr.a), VREG(d)); break;
        case TP_L: EMIT2(MOV, Q, ARG(vvr.t, vvr.a), VREG(d)); break;
        case TP_S: EMIT2(MOVS, S, ARG(vvr.t, vvr.a), VREG(d)); break;
        case TP_D: EMIT2(MOVS, D, ARG(vvr.t, vvr.a), VREG(d)); break;
        default:
            fail("unexpected copy type");
        }
    }
}

/* returns amount of stack used for passing args.
   note that this also writes to RAX. */
static uint32_t prep_call_args(
        Instr instr, uint32_t ret_ag,
        int *call_used_int_regs, int *call_used_sse_regs) {
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
        uint8_t arg_vreg_sz =
            (i == 0 && instr.u.call.args[i].t.t == TP_NONE)
                || instr.u.call.args[i].t.t == TP_AG
            ? X64_SZ_Q
            : get_vreg_sz(instr.u.call.args[i].t);
        /* note: %rax might be alive */
        VisitValueResult arg =
            visit_value_impl(instr.u.call.args[i].v, arg_vreg_sz, R_R11);
        int use_stack = (used_int_regs == countof(int_regs) &&
                         used_sse_regs == countof(sse_regs));
        ClassifyResult cr = {0};
        if (i == 0 && instr.u.call.args[i].t.t == TP_NONE) {
            /* QBE passes env using %rax,
               which is incompatible with varargs ABI. */
            EMIT2(MOV, Q, ARG(arg.t, arg.a), RAX);
            continue;
        } else {
            cr = classify(instr.u.call.args[i].t);
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
            EMIT2(MOV, Q, ARG(arg.t, arg.a), R11);
            for (j = 0; j < 2; ++j) {
                if (((uint8_t *) &cr)[j] == P_INTEGER) {
                    EMIT2(MOV, Q, MREG_OFF(R_R11, j * 8), FAKE);
                    LAST_INSTR.arg[1].mreg.mreg = int_regs[used_int_regs++];
                } else if (((uint8_t *) &cr)[j] == P_SSE) {
                    EMIT2(MOVS, D, MREG_OFF(R_R11, j * 8), FAKE);
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
                /* note: cannot use R11 here */
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

    *call_used_int_regs = used_int_regs;
    *call_used_sse_regs = used_sse_regs;
    return stk_arg_sz;
}

static void emit_call(Value f) {
    /* note: %rax might be alive due to prep_call_args */
    VisitValueResult vvr;
    switch (f.t) {
    case V_CSYM:
    case V_CTHS:
        EMIT1(CALL, Q, SYM(f.u.global_ident));
        return;
    case V_CI:
        EMIT2(MOV, Q, I64(f.u.u64), R11);
        EMIT1(CALL, Q, R11);
        return;
    case V_TMP:
        vvr = visit_value_impl(f, X64_SZ_Q, R_R11);
        EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R11);
        EMIT1(CALL, Q, R11);
        return;
    default:
        fail("unexpected func VALUE type");
        break; /* unreachable */
    }
}

static void isel_call(Instr instr) {
    uint32_t stk_arg_sz = 0;
    VReg ret = {0};
    uint32_t ret_ag = 0;
    ClassifyResult cr;
    int i;
    int call_used_int_regs = 0, call_used_sse_regs = 0;
    int used_int_regs = 0, used_sse_regs = 0;
    static uint8_t call_int_regs[] = {R_RDI, R_RSI, R_RDX, R_RCX, R_R8, R_R9};
    static uint8_t call_sse_regs[] = {
        R_XMM0, R_XMM1, R_XMM2, R_XMM3, R_XMM4, R_XMM5, R_XMM6, R_XMM7};

    if (instr.ret_t.t != TP_NONE) {
        uint8_t vreg_sz = X64_SZ_Q;
        if (instr.ret_t.t != TP_AG)
            vreg_sz = get_vreg_sz(instr.ret_t);
        ret = find_or_alloc_tmp(instr.ident, vreg_sz);
        if (instr.ret_t.t == TP_AG) {
            if (Type_log_align(instr.ret_t) == 4) /* align=16 */
                asm_func.alloc_sz = (asm_func.alloc_sz + 15) & ~15;
            ret_ag = asm_func.alloc_sz;
            asm_func.alloc_sz += Type_size(instr.ret_t);
            asm_func.alloc_sz = (asm_func.alloc_sz + 7) & ~7;
            EMIT2(LEA, Q, ALLOC(ret_ag), VREG(ret));
        }
    }

    EMIT2(SUB, Q, I64(0), RSP); /* for dynalloc */
    stk_arg_sz = prep_call_args(
            instr, ret_ag, &call_used_int_regs, &call_used_sse_regs);
    emit_call(instr.u.call.f);
    EMIT2(ADD, Q, I64(0), RSP); /* for dynalloc */

    /* dummy use/def marker for reg alloc */
    for (i = 0; i < call_used_int_regs; ++i)
        EMIT1(_DUMMY_USE, NONE, MREG(call_int_regs[i], Q));
    for (i = 0; i < call_used_sse_regs; ++i)
        EMIT1(_DUMMY_USE, NONE, MREG(call_sse_regs[i], D));
    for (i = 0; i < (int) countof(call_int_regs); ++i)
        EMIT1(_DUMMY_DEF, NONE, MREG(call_int_regs[i], Q));
    for (i = 0; i < (int) countof(call_sse_regs); ++i)
        EMIT1(_DUMMY_DEF, NONE, MREG(call_sse_regs[i], D));
    EMIT1(_DUMMY_USE, NONE, RAX);
    EMIT1(_DUMMY_DEF, NONE, RAX);
    EMIT1(_DUMMY_DEF, NONE, MREG(R_XMM8, D));
    EMIT1(_DUMMY_DEF, NONE, MREG(R_XMM9, D));
    EMIT1(_DUMMY_DEF, NONE, MREG(R_XMM10, D));
    EMIT1(_DUMMY_DEF, NONE, MREG(R_XMM11, D));
    EMIT1(_DUMMY_DEF, NONE, MREG(R_XMM12, D));
    EMIT1(_DUMMY_DEF, NONE, MREG(R_XMM13, D));

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
    } else if (instr.ret_t.t != TP_NONE) {
        switch (instr.ret_t.t) {
        case TP_W: EMIT2(MOV, L, MREG(R_RAX, L), VREG(ret)); break;
        case TP_L: EMIT2(MOV, Q, MREG(R_RAX, Q), VREG(ret)); break;
        case TP_S: EMIT2(MOVS, S, MREG(R_XMM0, S), VREG(ret)); break;
        case TP_D: EMIT2(MOVS, D, MREG(R_XMM0, D), VREG(ret)); break;
        default:
            /* note: QBE allows SUBWTY in arg/ret of call, but doesn't have
               any test for it, and it doesn't seem widely used */
            fail("unsupported call return type: %d", instr.ret_t.t);
        }
    }

    if (stk_arg_sz > asm_func.stk_arg_sz)
        asm_func.stk_arg_sz = stk_arg_sz;
}

static void isel_vastart(Instr instr) {
    /* note: cannot use %r11 */
    VisitValueResult p = visit_value(instr.u.args[0], X64_SZ_Q);
    EMIT2(MOV, Q, ARG(p.t, p.a), R10);

    EMIT2(MOV, L, I64(ctx.gp_offset), MREG_OFF(R_R10, 0));
    EMIT2(MOV, L, I64(ctx.fp_offset), MREG_OFF(R_R10, 4));
    EMIT2(LEA, Q, PREV_STK_ARG(ctx.overflow_arg_area), MREG_OFF(R_R10, 8));
    EMIT2(LEA, Q, ALLOC(ctx.reg_save_area), MREG_OFF(R_R10, 16));
}

static void isel_vaarg(Instr instr) {
    static uint32_t buf_suffix = 0;
    char buf[100];
    Ident else_label, end_label;

    VReg r = find_or_alloc_tmp(instr.ident, get_vreg_sz(instr.ret_t));
    VisitValueResult vvr = visit_value(instr.u.args[0], X64_SZ_Q);
    EMIT2(MOV, Q, ARG(vvr.t, vvr.a), R10);

    w_snprintf(buf, sizeof(buf), "@wqbe_vaarg_%u", buf_suffix++);
    else_label = Ident_from_str(buf);
    w_snprintf(buf, sizeof(buf), "@wqbe_vaarg_%u", buf_suffix++);
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
            EMIT2(MOVS, S, MREG_OFF(R_R11, 0), VREG(r));
        else
            EMIT2(MOVS, D, MREG_OFF(R_R11, 0), VREG(r));
        EMIT2(ADD, Q, I64(8), OVERFLOW_ARG_AREA);
        EMIT1(JMP, NONE, SYM(end_label));

        /* else:
               *r = *(reg_save_area + fp_offset)
               fp_offset += 16; */
        emit_label(else_label);
        EMIT2(MOV, L, FP_OFFSET, R11D);
        EMIT2(ADD, Q, REG_SAVE_AREA, R11);
        if (instr.ret_t.t == TP_S)
            EMIT2(MOVS, S, MREG_OFF(R_R11, 0), VREG(r));
        else
            EMIT2(MOVS, D, MREG_OFF(R_R11, 0), VREG(r));
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
            EMIT2(MOV, L, MREG_OFF(R_R11, 0), VREG(r));
        else
            EMIT2(MOV, Q, MREG_OFF(R_R11, 0), VREG(r));
        EMIT2(ADD, Q, I64(8), OVERFLOW_ARG_AREA);
        EMIT1(JMP, NONE, SYM(end_label));

        /* else:
               *r = *(reg_save_area + gp_offset)
               gp_offset += 8; */
        emit_label(else_label);
        EMIT2(MOV, L, GP_OFFSET, R11D);
        EMIT2(ADD, Q, REG_SAVE_AREA, R11);
        if (instr.ret_t.t == TP_W)
            EMIT2(MOV, L, MREG_OFF(R_R11, 0), VREG(r));
        else
            EMIT2(MOV, Q, MREG_OFF(R_R11, 0), VREG(r));
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
    EMIT0(UD2, NONE);
}

static void isel_jmp(Instr instr) {
    EMIT1(JMP, NONE, SYM(instr.u.jump.dst));
}

static void isel_jnz(Instr instr) {
    /* QBE requires cond to be of i32 type;
       i64 is also allowed but higher 32 bits are discarded. */
    VisitValueResult vvr = visit_value(instr.u.jump.v, X64_SZ_L);
    vvr = visit_value_avoid_imm32(vvr, X64_SZ_L);
    EMIT2(CMP, L, I64(0), ARG(vvr.t, vvr.a));
    EMIT1(JNE, NONE, SYM(instr.u.jump.dst));
    EMIT1(JMP, NONE, SYM(instr.u.jump.dst_else));
}

static void isel_ret(Instr instr) {
    int used_int_regs = 0, used_sse_regs = 0;
    if (instr.u.jump.v.t != V_UNKNOWN) {
        VisitValueResult vvr = visit_value(instr.u.jump.v, X64_SZ_Q);
        if (ctx.fd.ret_t.t == TP_AG) {
            ClassifyResult cr = classify(ctx.fd.ret_t);
            if (cr.fst == P_MEMORY) {
                uint32_t tp_sz = Type_size(ctx.fd.ret_t);
                /* RAX: required by ABI */
                EMIT2(MOV, Q, ALLOC(ctx.ret_ptr_alloc_offset), RAX);
                EMIT2(MOV, Q, ARG(vvr.t, vvr.a), RDI);
                blit(MREG_OFF(R_RDI, 0), MREG_OFF(R_RAX, 0), tp_sz);
            } else {
                int i;
                uint8_t *crp = (void*) &cr;
                EMIT2(MOV, Q, ARG(vvr.t, vvr.a), RDI);
                for (i = 0; i < 2; ++i) {
                    if (crp[i] == P_SSE) {
                        EMIT2(MOVS, D, MREG_OFF(R_RDI, i * 8), FAKE);
                        LAST_INSTR.arg[1].mreg.mreg =
                            used_sse_regs == 0 ? R_XMM0 : R_XMM1;
                        LAST_INSTR.arg[1].mreg.size = LAST_INSTR.size;
                        used_sse_regs++;
                    } else if (crp[i] == P_INTEGER) {
                        EMIT2(MOV, Q, MREG_OFF(R_RDI, i * 8), FAKE);
                        LAST_INSTR.arg[1].mreg.mreg =
                            used_int_regs == 0 ? R_RAX : R_RDX;
                        used_int_regs++;
                    }
                }
            }
        } else {
            switch (ctx.fd.ret_t.t) {
#define SRC ARG(vvr.t, vvr.a)
            case TP_W:
                if (vvr.t == AP_VREG)
                    vvr.a.vreg.size = X64_SZ_L;
                EMIT2(MOV, L, SRC, MREG(R_RAX, L));
                used_int_regs++;
                break;
            case TP_L:
                if (vvr.t == AP_VREG)
                    vvr.a.vreg.size = X64_SZ_Q;
                EMIT2(MOV, Q, SRC, RAX);
                used_int_regs++;
                break;
            case TP_S:
                if (vvr.t == AP_VREG)
                    vvr.a.vreg.size = X64_SZ_S;
                EMIT2(MOVS, S, SRC, XMM0);
                used_sse_regs++;
                break;
            case TP_D:
                if (vvr.t == AP_VREG)
                    vvr.a.vreg.size = X64_SZ_D;
                EMIT2(MOVS, D, SRC, XMM0);
                used_sse_regs++;
                break;
            case TP_SB:
            case TP_UB:
                if (vvr.t == AP_VREG)
                    vvr.a.vreg.size = X64_SZ_B;
                EMIT2(MOV, B, SRC, MREG(R_RAX, B));
                used_int_regs++;
                break;
            case TP_SH:
            case TP_UH:
                if (vvr.t == AP_VREG)
                    vvr.a.vreg.size = X64_SZ_W;
                EMIT2(MOV, W, SRC, MREG(R_RAX, W));
                used_int_regs++;
                break;
#undef SRC
            default:
                fail("FUNCDEF must return [ABITY]");
            }
        }
    }

    while (used_int_regs > 0) {
        if (used_int_regs == 1)
            EMIT1(_DUMMY_USE, NONE, RAX);
        else
            EMIT1(_DUMMY_USE, NONE, RDX);
        used_int_regs--;
    }
    while (used_sse_regs > 0) {
        if (used_sse_regs == 1)
            EMIT1(_DUMMY_USE, NONE, XMM0);
        else
            EMIT1(_DUMMY_USE, NONE, XMM1);
        used_sse_regs--;
    }

    EMIT2(MOV, Q, RBP, RSP);
    EMIT1(POP, Q, RBP);
    EMIT0(RET, NONE);
}

static void isel_dbgloc(Instr instr) {
    EMIT2(_AS_LOC, NONE,
          I64(instr.u.args[0].u.u64),
          I64(instr.u.args[1].t == V_CI
              ? instr.u.args[1].u.u64
              : (uint64_t) -1));
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

AsmFunc *isel_x64(FuncDef *fd) {
    uint16_t blk_id;
    Block blk;
    Instr *instr;

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

        instr = blk.dummy_head->next;
        for (; instr != blk.dummy_tail; instr = instr->next) {
            isel(*instr);
        }
        ctx.is_first_blk = 0;
    }

    /* ensure space for end marker (0) of instr and label */
    assert(ctx.instr_cnt < countof(asm_func.instr));
    assert(ctx.label_cnt < countof(asm_func.label));
    return &asm_func;
}
