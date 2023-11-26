/*
 * System V ABI on AMD64, simplified for QBE-supported types:
 *
 * struct/union/array classification:
 *     1. if size > 16 bytes, MEMORY for the whole type;
 *        (or if contains unaligned fields -- unlikely in practice)
 *     2. for each eightbyte:
 *        - (impossible?) if the whole eightbyte is padding: ignore
 *        - if all non-padding fields are float/double: SSE
 *        - otherwise: INTEGER
 *
 * parameter passing:
 *     MEMORY: use stack
 *     SSE: next available %xmm0-%xmm7; then stack
 *     INTEGER: next available %rdi, %rsi, %rdx, %rcx, %r8, %r9; then stack
 *
 * parameter returning:
 *     MEMORY: hidden arg in %rdi; %rax returns initial %rdi
 *     SSE: next available %xmm0, %xmm1
 *     INTEGER: next available %rax, %rdx
 *
 *
 * alignment requirements:
 *     - An array uses the same alignment as its elements, except that a local
 *       or global array variable of length at least 16 bytes or a C99
 *       variable-length array variable always has alignment of at least 16
 *       bytes.
 *     - The end of the input argument area shall be aligned on a 16 byte
 *       boundary. In other words, the stack needs to be 16 byte aligned
 *       immediately before the call instruction is executed.
 *
 * varargs-/stdargs- specific:
 *     %al is used as hidden argument to specify the number of vector registers
 *     used (%xmm0-%xmm7).
 */

enum {
    R_RAX,
    R_RBX, /* callee-saved */
    R_RCX,
    R_RDX,
    R_RSI,
    R_RDI,
    R_RBP,
    R_RSP,
    R_R8,
    R_R9,
    R_R10, /* scratch */
    R_R11, /* scratch */
    R_R12, /* callee-saved */
    R_R13, /* callee-saved */
    R_R14, /* callee-saved */
    R_R15, /* callee-saved */
    R_XMM0,
    R_XMM1,
    R_XMM2,
    R_XMM3,
    R_XMM4,
    R_XMM5,
    R_XMM6,
    R_XMM7,
    R_XMM8, /* scratch */
    R_XMM9, /* scratch */
    R_XMM10, /* scratch */
    R_XMM11, /* scratch */
    R_XMM12, /* scratch */
    R_XMM13, /* scratch */
    R_XMM14, /* scratch */
    R_XMM15, /* scratch */
    R_END /* does not exist in x64 */
};

enum AsmInstrType {
    A_UNKNOWN = 0, /* required */
#define A(up,low) A_##up,
#include "x64.inc"
#undef A
    A_END
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
