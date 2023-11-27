#include <assert.h>
#include <string.h>

#include "all.h"
#include "x64.h"

static struct {
    AsmFunc *in_ptr;
    uint32_t i_ip, i_lp;
    AsmFunc out;
    uint32_t o_ip, o_lp;
} ctx;

#define IN (*(ctx.in_ptr))
#define OUT (ctx.out)
#define I_IP (ctx.i_ip)
#define I_LP (ctx.i_lp)
#define O_IP (ctx.o_ip)
#define O_LP (ctx.o_lp)

static void visit_arg(AsmInstr *in, int idx) {
    /* ensure the whole union is zero-ed */
    AsmInstrArg arg = {0};

    switch (in->arg_t[idx]) {
    case AP_NONE: case AP_I64: case AP_SYM: case AP_MREG:
        return;
    case AP_VREG:
        fail("unexpected AP_VREG; not supported by naive reg alloc");
        return; /* unreachable */
    case AP_F32: case AP_F64:
        return; /* TODO: fix fp imm */
    case AP_STK_ARG:
        arg.mreg.size = X64_SZ_Q;
        arg.mreg.mreg = R_RSP;
        arg.mreg.is_deref = 1;
        arg.mreg.offset = in->arg[idx].offset;
        in->arg[idx] = arg;
        in->arg_t[idx] = AP_MREG;
        return;
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
        emit_instr(in);
        return;
    }

    /* skip other jmp ops, in which symbols could have different meanings */
    if (in.t == A_JNE) {
        /* note: we could also optimize
           this: jne .a ; jmp .b ; .a: bar
           to:   je  .b ;          .a: bar */
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
        case A_AND:
        case A_CMP:
        case A_LEA:
        case A_MOV:
        case A_MOVS:
        case A_SUB:
            break;
        default:
            fail("unsupported mem-mem op found: %s", op_table[in.t]);
            return; /* unreachable */
        }

        /* leaq -16(%rbp), 8(%rsp)
           => leaq -16(%rbp), %r11
              movq %r11, 8(%rsp)

           subq -16(%rbp), 8(%rsp)
           => movq -16(%rbp), %r11
              subq %r11, 8(%rsp)

           movss -16(%rbp), 8(%rsp)
           => movss -16(%rbp), %xmm8
              movss %xmm8, 8(%rsp) */
        tmp.mreg.size = in.size;
        tmp.mreg.mreg = (in.size == SZ_S || in.size == SZ_D) ? R_XMM8 : R_R11;
        emit_instr(in);
        if (in.t != A_LEA) OUT.instr[O_IP - 1].t = A_MOV;
        OUT.instr[O_IP - 1].arg[1] = tmp;
        emit_instr(in);
        if (in.t == A_LEA) OUT.instr[O_IP - 1].t = A_MOV;
        OUT.instr[O_IP - 1].arg[0] = tmp;
        return;
    }

    /* TODO: fix call with dynalloc */
    emit_instr(in);
}

AsmFunc *ra_naive_x64(AsmFunc *in_ptr) {
    memset(&ctx, 0, sizeof(ctx));
    ctx.in_ptr = in_ptr;

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
            OUT.label[O_LP].ident = IN.label[I_LP].ident;
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
    return &ctx.out;
}