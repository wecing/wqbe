#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"
#include "x64.h"

static struct {
    AsmFunc *in_ptr;
    uint32_t i_ip, i_lp;
    AsmFunc out;
    uint32_t o_ip, o_lp;

    uint32_t fn_id;
    uint16_t *first_dd_id_ptr;
} ctx;

static Ident rewrite_label(Ident ident) {
    char buf[50];
    if (Ident_to_str(ident)[0] != '@')
        return ident; /* only rewrite local labels */
    w_snprintf(buf, sizeof(buf), "@wqbe_ra_%u_%u_%u",
               ctx.fn_id, ident.slot, ident.idx);
    return Ident_from_str(buf);
}

static AsmInstr rewrite_jmp_label(AsmInstr in) {
    switch (in.t) {
    case A_JMP:
    case A_JNE:
    case A_JE:
    case A_JL:
        in.arg[0].sym.ident = rewrite_label(in.arg[0].sym.ident);
        return in;
    }
    fail("unexpected jump op");
    return in; /* unreachable */
}

#define IN (*(ctx.in_ptr))
#define OUT (ctx.out)
#define I_IP (ctx.i_ip)
#define I_LP (ctx.i_lp)
#define O_IP (ctx.o_ip)
#define O_LP (ctx.o_lp)

static Ident next_fp_ident(void) {
    static int n = 0;
    char buf[30];
    w_snprintf(buf, sizeof(buf), "$.wqbe.fp.%d", n++);
    return Ident_from_str(buf);
}

static Ident next_quad_ident(void) {
    static int n = 0;
    char buf[30];
    w_snprintf(buf, sizeof(buf), "$.wqbe.quad.%d", n++);
    return Ident_from_str(buf);
}

static void visit_arg(AsmInstr *in, int idx) {
    /* ensure the whole union is zero-ed */
    AsmInstrArg arg = {0};

    switch (in->arg_t[idx]) {
    case AP_NONE: case AP_SYM: case AP_MREG:
        return;
    case AP_VREG:
        fail("unexpected AP_VREG; not supported by naive reg alloc");
        return; /* unreachable */
    case AP_I64: {
        /* convert imm64 to .quad data if needed.
           note that we still need to e.g. truncate to i8 for addb; this is done
           in dump_arg(). */
        uint16_t dd_id;
        DataDef *dd;
        int64_t i64 = in->arg[idx].i64;
        if (-0x80000000L <= i64 && i64 <= 0x7FFFFFFFL)
            /* cvtsi2s{s,d} do not accept immediates,
               so always use .quad data */
            if (in->t != A_CVTSI2SS && in->t != A_CVTSI2SD)
                return;
        dd_id = DataDef_alloc(next_quad_ident());
        dd = DataDef_get(dd_id);
        dd->linkage.is_section = 1;
#if defined(__OpenBSD__) || defined(__linux__)
        dd->linkage.sec_name = w_strdup(".rodata");
#else
        dd->linkage.sec_name = w_strdup("__TEXT,__literal8");
#endif
        dd->log_align = 3;
        dd->next_id = *ctx.first_dd_id_ptr;
        *ctx.first_dd_id_ptr = dd_id;
        dd->items = calloc(2, sizeof(dd->items[0]));
        dd->items[0].is_ext_ty = 1;
        dd->items[0].u.ext_ty.t.t = TP_L;
        dd->items[0].u.ext_ty.items =
            calloc(2, sizeof(dd->items[0].u.ext_ty.items[0]));
        dd->items[0].u.ext_ty.items[0].t = DI_CONST;
        dd->items[0].u.ext_ty.items[0].u.cst.t = V_CI;
        dd->items[0].u.ext_ty.items[0].u.cst.u.u64 = i64;
        dd->items[1].is_dummy_item = 1;
        arg.sym.ident = dd->ident;
        in->arg[idx] = arg;
        in->arg_t[idx] = AP_SYM;
        return;
    }
    case AP_F32: {
        uint32_t v = *(uint32_t *) &in->arg[idx].f32;
        uint16_t dd_id = DataDef_alloc(next_fp_ident());
        DataDef *dd = DataDef_get(dd_id);
        dd->linkage.is_section = 1;
#if defined(__OpenBSD__) || defined(__linux__)
        dd->linkage.sec_name = w_strdup(".rodata");
#else
        dd->linkage.sec_name = w_strdup("__TEXT,__literal8");
#endif
        dd->log_align = 3;
        dd->next_id = *ctx.first_dd_id_ptr;
        *ctx.first_dd_id_ptr = dd_id;
        dd->items = calloc(2, sizeof(dd->items[0]));
        dd->items[0].is_ext_ty = 1;
        dd->items[0].u.ext_ty.t.t = TP_W;
        dd->items[0].u.ext_ty.items =
            calloc(2, sizeof(dd->items[0].u.ext_ty.items[0]));
        dd->items[0].u.ext_ty.items[0].t = DI_CONST;
        dd->items[0].u.ext_ty.items[0].u.cst.t = V_CI;
        dd->items[0].u.ext_ty.items[0].u.cst.u.u64 = v;
        dd->items[1].is_dummy_item = 1;
        arg.sym.ident = dd->ident;
        in->arg[idx] = arg;
        in->arg_t[idx] = AP_SYM;
        return;
    }
    case AP_F64: {
        uint64_t v = *(uint64_t *) &in->arg[idx].f64;
        uint16_t dd_id = DataDef_alloc(next_fp_ident());
        DataDef *dd = DataDef_get(dd_id);
        dd->linkage.is_section = 1;
#if defined(__OpenBSD__) || defined(__linux__)
        dd->linkage.sec_name = w_strdup(".rodata");
#else
        dd->linkage.sec_name = w_strdup("__TEXT,__literal8");
#endif
        dd->log_align = 3;
        dd->next_id = *ctx.first_dd_id_ptr;
        *ctx.first_dd_id_ptr = dd_id;
        dd->items = calloc(2, sizeof(dd->items[0]));
        dd->items[0].is_ext_ty = 1;
        dd->items[0].u.ext_ty.t.t = TP_L;
        dd->items[0].u.ext_ty.items =
            calloc(2, sizeof(dd->items[0].u.ext_ty.items[0]));
        dd->items[0].u.ext_ty.items[0].t = DI_CONST;
        dd->items[0].u.ext_ty.items[0].u.cst.t = V_CI;
        dd->items[0].u.ext_ty.items[0].u.cst.u.u64 = v;
        dd->items[1].is_dummy_item = 1;
        arg.sym.ident = dd->ident;
        in->arg[idx] = arg;
        in->arg_t[idx] = AP_SYM;
        return;
    }
    case AP_ALLOC:
        arg.mreg.size = X64_SZ_Q;
        arg.mreg.mreg = R_RBP;
        arg.mreg.is_deref = 1;
        arg.mreg.offset = -IN.alloc_sz + in->arg[idx].offset;
        in->arg[idx] = arg;
        in->arg_t[idx] = AP_MREG;
        return;
    default:
        fail("unrecognized AsmInstr.arg_t");
        return; /* unreachable */
    }
}

static void emit_instr(AsmInstr x) {
    OUT.instr[O_IP++] = x;
    assert(O_IP < countof(OUT.instr));
}

static int is_mem_arg(uint8_t arg_t, AsmInstrArg arg) {
    return arg_t == AP_SYM || (arg_t == AP_MREG && arg.mreg.is_deref);
}

static void visit_instr(void) {
    AsmInstr in = IN.instr[I_IP];

    /* QBE allows representing f32/f64 literals as u64 blob */
    if (in.t == A_CVTSS2S || in.t == A_CVTTSS2SI) {
        if (in.arg_t[0] == AP_I64) in.arg_t[0] = AP_F32;
    } else if (in.t == A_CVTSD2S || in.t == A_CVTTSD2SI) {
        if (in.arg_t[0] == AP_I64) in.arg_t[0] = AP_F64;
    } else {
        if (in.size == SZ_S) {
            if (in.arg_t[0] == AP_I64) in.arg_t[0] = AP_F32;
            if (in.arg_t[1] == AP_I64) in.arg_t[1] = AP_F32;
        } else if (in.size == SZ_D) {
            if (in.arg_t[0] == AP_I64) in.arg_t[0] = AP_F64;
            if (in.arg_t[1] == AP_I64) in.arg_t[1] = AP_F64;
        }
    }

    visit_arg(&in, 0);
    visit_arg(&in, 1);

    /* eliminate no-op jmp.
       e.g.:                bar ; jmp .b
                .a: .b: .c: baz
       becomes:             bar
                .a: .b: .c: baz */
    if (in.t == A_JMP) {
        uint32_t lp = I_LP;
        while (IN.label[lp].offset == I_IP + 1) {
            if (Ident_eq(IN.label[lp].ident, in.arg[0].sym.ident))
                return; /* skip current jmp */
            lp++;
        }
        emit_instr(rewrite_jmp_label(in));
        return;
    }

    /* skip other jmp ops, in which symbols could have different meanings */
    if (in.t == A_JNE || in.t == A_JE || in.t == A_JL) {
        /* note: we could also optimize
           this: jne .a ; jmp .b ; .a: bar
           to:   je  .b ;          .a: bar */
        emit_instr(rewrite_jmp_label(in));
        return;
    }
    /* same for call; symbols are used as-is */
    if (in.t == A_CALL) {
        emit_instr(in);
        return;
    }

    /* eliminate mem-mem ops when not supported */
    if (is_mem_arg(in.arg_t[0], in.arg[0]) &&
        is_mem_arg(in.arg_t[1], in.arg[1])) {
        static const char *op_table[] = {
            0, /* A_UNKNOWN */
#define A(up,low) #low,
#include "x64.inc"
#undef A
            0 /* A_END */
        };
        AsmInstrArg tmp = {0};

        switch (in.t) {
        case A_ADD:
        case A_ADDS:
        case A_AND:
        case A_CMP:
        case A_DIVS:
        case A_IMUL:
        case A_LEA:
        case A_MOV:
        case A_MOVS:
        case A_MOVSB:
        case A_MOVSL:
        case A_MOVSW:
        case A_MOVZB:
        case A_MOVZW:
        case A_MULS:
        case A_OR:
        case A_SUB:
        case A_SUBS:
        case A_UCOMIS:
        case A_XOR:
            break;
        default:
            fail("unsupported mem-mem op found: %s", op_table[in.t]);
            return; /* unreachable */
        }

        /* leaq -16(%rbp), 8(%rsp)
           => leaq -16(%rbp), %r11
              movq %r11, 8(%rsp)

           subl -16(%rbp), 8(%rsp)
           => movl -16(%rbp), %r11d
              subl %r11d, 8(%rsp)

           movss -16(%rbp), 8(%rsp)
           => movss -16(%rbp), %xmm15
              movss %xmm15, 8(%rsp)

           subsd $.fp0(%rip), -12(%rbp)
           => movsd $.fp0(%rip), %xmm15
              subsd %xmm15, -12(%rbp) */
        tmp.mreg.size = in.size;
        tmp.mreg.mreg = (in.size == SZ_S || in.size == SZ_D) ? R_XMM15 : R_R11;
        emit_instr(in);
        if (in.t != A_LEA)
            OUT.instr[O_IP - 1].t =
                tmp.mreg.mreg == R_XMM15 ? A_MOVS : A_MOV;
        OUT.instr[O_IP - 1].arg_t[1] = AP_MREG;
        OUT.instr[O_IP - 1].arg[1] = tmp;
        emit_instr(in);
        if (in.t == A_LEA) OUT.instr[O_IP - 1].t = A_MOV;
        OUT.instr[O_IP - 1].arg_t[0] = AP_MREG;
        OUT.instr[O_IP - 1].arg[0] = tmp;
        return;
    }

    /* fix call with dynalloc */
    if (I_IP > 2 && /* prologue might contain subq $0, %rsp */
        (in.t == A_ADD || in.t == A_SUB) &&
        in.arg_t[0] == AP_I64 &&
        in.arg[0].i64 == 0 &&
        in.arg_t[1] == AP_MREG &&
        in.arg[1].mreg.size == X64_SZ_Q &&
        in.arg[1].mreg.mreg == R_RSP &&
        !in.arg[1].mreg.is_deref) {
        /* rewrite addq $0, %rsp and subq $0, %rsp */
        in.arg[0].i64 = IN.stk_arg_sz;
        /* skip if no-op */
        if (in.arg[0].i64 == 0)
            return;
    }

    emit_instr(in);
}

AsmFunc *ra_naive_x64(AsmFunc *in_ptr, uint16_t *first_datadef_id_ptr) {
    uint32_t fn_id = ctx.fn_id;
    memset(&ctx, 0, sizeof(ctx));
    ctx.in_ptr = in_ptr;
    ctx.fn_id = fn_id;
    ctx.first_dd_id_ptr = first_datadef_id_ptr;

    /* ensure both are 16-byte aligned */
    IN.alloc_sz = (IN.alloc_sz + 15) & ~15;
    IN.stk_arg_sz = (IN.stk_arg_sz + 15) & ~15;
    /* fix sub $0, %rsp in prologue */
    IN.instr[2].arg[0].i64 = IN.alloc_sz;
    if (!IN.has_dyn_alloc) {
        /* no dyn alloc: pre-allocate ALLOC and STK_ARG
           with dyn alloc: also dyn alloc STK_ARG */
        IN.instr[2].arg[0].i64 += IN.stk_arg_sz;
    }

    while (IN.instr[I_IP].t) {
        /* copy labels for current input instr */
        while (!Ident_is_empty(IN.label[I_LP].ident) &&
               IN.label[I_LP].offset == I_IP) {
            OUT.label[O_LP].ident = rewrite_label(IN.label[I_LP].ident);
            OUT.label[O_LP].offset = O_IP;
            I_LP++;
            O_LP++;
        }

        visit_instr();

        I_IP++;
    }

    /* ensure space for end marker (0) of instr and label */
    assert(O_IP < countof(OUT.instr));
    assert(O_LP < countof(OUT.label));
    ctx.fn_id++;
    return &ctx.out;
}
