#include <stdint.h>
#include <stdio.h>

#define countof(x) (sizeof(x) / sizeof((x)[0]))

typedef struct Ident {
    uint16_t slot; /* hash table slot */
    uint16_t idx; /* idx within slot */
} Ident;

/* IR: all "_id" fields (e.g. instr_id, ag_id) mean null if set to 0 */

typedef struct Value {
    enum {
        V_UNKNOWN,
        /* constants */
        V_CI,
        V_CS,
        V_CD,
        V_CSYM,
        V_CTHS,
        /* SSA values */
        V_TMP
    } t;
    union {
        uint64_t u64;
        float s;
        double d;
        Ident global_ident; /* global symbol, i.e. $IDENT */
        /* DYNCONST := CONST | 'thread' $IDENT */
        Ident thread_ident;

        Ident tmp_ident; /* func-scope tmps, i.e. %IDENT */
    } u;
} Value;

/* Type.t */
enum {
    TP_UNKNOWN,
    /* BASETY := 'w' | 'l' | 's' | 'd' */
    TP_W,
    TP_L,
    TP_S,
    TP_D,
    /* EXTTY := BASETY | 'b' | 'h' */
    TP_B,
    TP_H,
    /* SUBTY := EXTTY | :IDENT */
    TP_AG,
    /* SUBWTY := 'sb' | 'ub' | 'sh' | 'uh' */
    /* ABITY := BASETY | SUBWTY | :IDENT */
    TP_SB,
    TP_UB,
    TP_SH,
    TP_UH,
    /* where type is optional, e.g. func return type is [ABITY];
       or for 'env' params/args, which have no type */
    TP_NONE
};

typedef struct Type {
    uint32_t t:4;
    uint32_t ag_id:28;
} Type;

typedef struct ArrType {
    Type t;
    uint32_t count;
} ArrType;

typedef struct AgType {
    uint32_t log_align:3; /* max align 1<<7 == 128 reserved for unspecified */
    uint32_t is_opaque:1;
    uint32_t is_union:1;
    uint32_t size:27;
    Ident ident;
    union {
        ArrType *sb; /* struct body; terminated with TP_UNKNOWN */
        ArrType **ub; /* union body; terminated with NULL + TP_UNKNOWN */
    } u;
} AgType;

typedef struct Linkage {
    uint8_t is_export;
    uint8_t is_thread;
    uint8_t is_section;
    char *sec_name;
    char *sec_flags;
} Linkage;

typedef struct DataItem {
    enum {
        DI_UNKNOWN,
        DI_SYM_OFF,
        DI_STR,
        DI_CONST
    } t;
    union {
        struct {
            Ident ident;
            int32_t offset;
        } sym_off;
        char *str;
        Value cst;
    } u;
} DataItem;

typedef struct DataDefItem {
    uint8_t is_dummy_item;
    uint8_t is_ext_ty;
    union {
        struct {
            Type t;
            DataItem *items; /* ends with DI_UNKNOWN */
        } ext_ty;
        uint32_t zero_size;
    } u;
} DataDefItem;

typedef struct DataDef {
    Linkage linkage;
    Ident ident;
    /* log_align is optional; 0xFF == not provided.
       From QBE spec:
           when no alignment is provided, the maximum alignment
           from the platform is used. */
    uint8_t log_align;
    uint16_t next_id;
    DataDefItem *items; /* ends with is_dummy_item */
} DataDef;

/* Instr.t */
enum {
    I_UNKNOWN,
#define I(up,low) I_##up,
#include "instr.inc"
#undef I
    I_END
};

typedef struct Instr Instr;
struct Instr {
    uint32_t t:8;
    Type ret_t;
    Ident ident; /* optional */
    uint32_t blit_sz; /* I_BLIT only */
    union {
        Value args[2];
        struct {
            Value f;
            /* args[i] where i >= va_begin_idx are varargs.
               when va_begin_idx >= len(args), no varargs are provided.
               when va_begin_idx > len(args), called func is not varargs.*/
            uint16_t va_begin_idx;
            struct {
                Type t;
                Value v;
            } *args; /* ends with TP_UNKNOWN */
        } call;
        struct {
            struct {
                Ident ident;
                Value v;
            } *args; /* ends with V_UNKNOWN */
        } phi;
        struct {
            Value v; /* jnz, ret */
            Ident dst; /* jmp, jnz */
            Ident dst_else; /* jnz */
        } jump;
    } u;
    Instr *prev;
    Instr *next;
};

typedef struct Block {
    Ident ident;
    uint16_t next_id;
    Instr *dummy_head;
    Instr *dummy_tail;
} Block;

typedef struct FuncDef {
    Linkage linkage;
    Type ret_t;
    Ident ident;
    struct {
        Type t;
        Ident ident;
    } *params; /* ends with TP_UNKNOWN */
    uint8_t is_varargs;
    uint16_t dbgfile_id; /* 0: not provided */
    uint16_t blk_id;
    uint16_t next_id;
} FuncDef;

/* asm: AsmInstr.t and AsmInstr.u.mreg.mreg are platform-specific enum */

typedef union AsmInstrArg AsmInstrArg;

/* AsmInstr.size */
enum { SZ_NONE, SZ_B, SZ_H, SZ_W, SZ_L, SZ_S, SZ_D };
/* AsmInstr.arg_t */
enum {
    AP_NONE,
    AP_I64, AP_F32, AP_F64, AP_SYM, AP_MREG,
    /* these are removed in reg alloc */
    AP_VREG,
    /* AP_STK_ARG,
       stack-passed params on current frame;
       on x64 this is just n(%rsp) */
    /* AP_PREV_STK_ARG,
       stack-passed params on caller's frame;
       on x64 this is just 16+n(%rbp) */
    AP_ALLOC /* static stack allocation; also used as reg save area */
};
/* AsmInstr.arg.sym.t */
enum {
    /* e.g. xs+12(%rip)
       `leaq xs+12(%rip), %rax` retrieves addr of xs+12;
       `movq xs+12(%rip), %rax` retrieves data at xs+12. */
    AP_SYM_PLAIN,
    /* e.g. xs@GOTPCREL(%rip)
       ignores offset.
       `movq xs@GOTPCREL(%rip), %rax` retrieves addr of xs. */
    AP_SYM_GOTPCREL,
    /* e.g. x@tpoff+12; or x@tpoff+12(%r11)
       - `movq %fs:x@tpoff+12` retrieves thread-local data at x+12;
       - `movq %fs:0, %r11`
         `leaq x@tpoff+12(%r11), %r11`
         retrieves thread-local address of x+12. */
    AP_SYM_TPOFF
};

typedef struct AsmInstr {
    uint8_t t;
    uint8_t arg0_use_fs; /* 1st arg xxx becomes %fs:xxx */
    uint8_t size; /* SZ_xxx */
    uint8_t arg_t[2]; /* AP_xxx */
    union AsmInstrArg {
        int64_t i64;
        float f32;
        double f64;
        struct MSym {
            /* when used in jump ops, only ident is used. (e.g. jmp .BB0) */
            Ident ident;
            uint32_t t:2;
            uint32_t mreg:6; /* only for AP_SYM_TPOFF; may be R_END on x64 */
            int32_t offset:24;
        } sym;
        struct MReg {
            /* when is_deref=0, offset is ignored. with mreg=%rdi:
               is_deref=0 => %rdi
               is_deref=1 => (%rdi)
               is_deref=1, offset=12 => 12(%rdi) */
            uint8_t size; /* SZ_xxx */
            uint8_t mreg;
            uint32_t is_deref:1;
            int32_t offset:31;
        } mreg;
        struct VReg {
            uint8_t size; /* SZ_xxx */
            uint32_t id; /* > 0 */
        } vreg;
        int offset; /* byte offset */
    } arg[2];
} AsmInstr;

typedef struct AsmFunc {
    AsmInstr instr[128 * 1024]; /* 128 * 24KB; ends with .t == 0 (A_UNKNOWN) */
    struct {
        Ident ident;
        uint32_t offset; /* index into instr, inclusive */
    } label[128 * 128]; /* 128 * 1KB; ends with empty ident; sorted by offset */
    uint32_t stk_arg_sz;
    uint32_t alloc_sz;
    uint8_t has_dyn_alloc;
} AsmFunc;

/* ir.c */
Ident Ident_from_str(const char *);
const char *Ident_to_str(Ident);
int Ident_eq(Ident, Ident);
int Ident_is_empty(Ident);
int Type_is_subty(Type);
int Type_is_extty(Type);
int Type_is_abity(Type);
uint8_t Type_log_align(Type);
uint32_t Type_size(Type);
Type AgType_lookup_or_fail(Ident);
Type AgType_lookup_or_alloc(Ident);
AgType *AgType_get(Type);
uint16_t DataDef_alloc(Ident);
uint16_t DataDef_lookup(Ident);
DataDef *DataDef_get(uint16_t);
uint16_t FuncDef_alloc(Ident);
uint16_t FuncDef_lookup(Ident);
FuncDef *FuncDef_get(uint16_t);
uint16_t Block_alloc(void);
Block *Block_get(uint16_t);
void Block_append(Block *, Instr *);
void Block_append_before_jump(Block *, Instr *);
Instr *Instr_alloc(void);
void Instr_free(Instr *);
void Instr_dump(Instr);
void ir_fix_typedef_size_align(void);
uint16_t ir_add_dbgfile(const char *);
const char *ir_get_dbgfile(uint16_t);
void ir_foreach_dbgfile(void (*)(uint16_t, const char *));
void ir_dump_typedef(void);
void ir_dump_datadef(uint16_t);
void ir_dump_funcdef(uint16_t);
void ir_cleanup(void);

/* parse.c */
typedef struct ParseResult {
    uint16_t first_datadef_id;
    uint16_t first_funcdef_id;
} ParseResult;
ParseResult parse(FILE *);

/* util.c */
void check(int cond, const char *, ...); /* like assert(), but always enabled */
void fail(const char *, ...);
void dump_stacktrace(void);
char *w_strdup(const char *);
int w_snprintf(char *, size_t, const char *, ...);

/* dephi.c */
void dephi(FuncDef *);

/* isel_naive.c */
void dump_x64(AsmFunc *, Linkage, FILE *);
void dump_x64_data(DataDef, FILE *);
AsmFunc *isel_naive_x64(FuncDef *); /* returns borrowed memory */

/* ra_naive.c */
AsmFunc *ra_naive_x64(AsmFunc *, uint16_t *);

/* isel.c */
AsmFunc *isel_x64(FuncDef *); /* returns borrowed memory */
