#include <string.h>

#include "all.h"
#include "x64.h"

typedef struct UseDefSucc {
    /* def/use: ends with R_END; mreg id => id; vreg id => id+R_END */
    uint32_t def[2];
    uint32_t use[3];
    AsmInstr *succ[2]; /* ends with NULL */
} UseDefSucc;

enum GetRegIdFlag { USE, DEF };

static uint32_t
get_reg_id(uint8_t arg_t, union AsmInstrArg arg, enum GetRegIdFlag flag) {
    switch (arg_t) {
    case AP_MREG:
        /* writing to 12(%rax) does not def %rax */
        return flag == DEF && arg.mreg.is_deref ? R_END : arg.mreg.mreg;
    case AP_VREG:
        return arg.vreg.id + R_END;
    default:
        return R_END;
    }
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

static UseDefSucc get_uds(AsmFunc *fn, AsmInstr *ip) {
    UseDefSucc r = { {R_END, R_END}, {R_END, R_END, R_END}, {0, 0} };
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
        // TODO: USE unused regs, DEF ret regs
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

    switch (ip->t) {
    case A_RET: case A_UD2:
        r.succ[0] = 0;
        break;
    case A_JE: case A_JL: case A_JNE:
        r.succ[0] = ip + 1;
        r.succ[1] = get_instr_by_label(fn, ip->arg[0].sym.ident);
        break;
    case A_JMP:
        r.succ[0] = get_instr_by_label(fn, ip->arg[0].sym.ident);
        break;
    default:
        r.succ[0] = ip + 1;
        break;
    }
    verify_succ_ptr(fn, r.succ[0]);
    verify_succ_ptr(fn, r.succ[1]);

    return r;
}

AsmFunc *ra_x64(AsmFunc *in_ptr) {
    (void)in_ptr;
    return 0; // TODO: implement ra_x64
}
