#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define countof(x) (sizeof(x) / sizeof((x)[0]))

typedef struct Ident {
    uint16_t slot; /* hash table slot */
    uint16_t idx; /* idx within slot */
} Ident;

/* all "_id" fields (e.g. instr_id, ag_id) mean null if set to 0 */

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

typedef struct Type {
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
    uint32_t t:4;
    uint32_t ag_id:28;
} Type;

typedef struct ArrType {
    Type t;
    uint32_t count;
} ArrType;

typedef struct AgType {
    uint32_t log_align:3; /* max align 1<<7 == 128 */
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
    uint8_t log_align;
    uint16_t next_id;
    DataDefItem *items; /* ends with is_dummy_item */
} DataDef;

typedef struct Instr {
    enum {
        I_UNKNOWN,
#define I(up,low) I_##up,
#include "instr.inc"
#undef I
        I_END /* unused, required by C89 */
    };
    uint32_t t:8;
    uint32_t next_id:24;
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
            uint16_t args_len;
            struct {
                Ident ident;
                Value v;
            } *args;
        } phi;
        struct {
            Value v; /* jnz, ret */
            Ident dst; /* jmp, jnz */
            Ident dst_else; /* jnz */
        } jump;
    } u;
} Instr;

typedef struct Block Block;
struct Block {
    Ident ident;
    uint32_t instr_id; /* phi and regular instr chain */
    uint32_t jump_id; /* not a chain; exactly one */
    uint16_t next_id;
};

typedef struct FuncDef {
    Linkage linkage;
    Type ret_t;
    Ident ident;
    struct {
        Type t;
        Ident ident;
    } *params; /* ends with TP_UNKNOWN */
    uint8_t is_varargs;
    uint16_t blk_id;
    uint16_t next_id;
} FuncDef;

/* ir.c */
Ident Ident_from_str(const char *);
const char *Ident_to_str(Ident);
int Ident_eq(Ident, Ident);
int Type_is_subty(Type);
int Type_is_extty(Type);
int Type_is_abity(Type);
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
uint32_t Instr_alloc(void);
Instr *Instr_get(uint32_t);
void ir_dump_typedef(void);
void ir_dump_datadef(uint16_t);
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
