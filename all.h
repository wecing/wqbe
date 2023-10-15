#include <stdint.h>

typedef struct Ident {
  uint16_t slot; /* hash table slot */
  uint16_t idx; /* idx within slot */
} Ident;

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
    V_ID,
    V_SYM /* func param */
  } t;
  union {
    uint64_t u64;
    float s;
    double d;
    Ident ident;
    /* DYNCONST := CONST | 'thread' $IDENT */
    Ident thread_ident;

    uint32_t instr_id; /* idx into instr_pool; 0 means null */
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
    /* where type is optional, e.g. func return type is [ABITY] */
    TP_NONE
  };
  uint16_t t:4;
  uint32_t ag_id:28;
} Type;

typedef struct ArrType {
  Type t;
  uint32_t count;
} ArrType;

typedef struct AgType {
  uint32_t log_align:3; /* max align 1<<7 == 128 */
  uint32_t has_body:1;
  uint32_t body_len:14; /* max number of fields 2^14-1 == 16383 */
  uint32_t body_cap:14;
  uint32_t size;
  Ident ident;
  ArrType *body;
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
  uint8_t is_ext_ty;
  uint8_t ext_ty;
  uint32_t zero_size; /* only if !is_ext_ty */
  uint16_t items_len;
  uint16_t items_cap;
  DataItem *items;
} DataDefItem;

typedef struct DataDef {
  Linkage linkage;
  Ident ident;
  uint8_t log_align;
  uint16_t items_len;
  uint16_t items_cap;
  uint16_t next_id; /* idx into data_def_pool; 0 means null */
  DataDefItem *items;
} DataDef;

typedef struct Instr {
  enum {
    I_UNKNOWN,

    /* T: wlsd */
    /* I: wl */
    /* F: sd */
    /* m: (ptr type) */
    I_ADD, I_SUB, I_DIV, I_MUL, /* T(T, T) */
    I_NEG, /* T(T, T) */
    I_UDIV, I_REM, I_UREM, /* I(I, I) */
    I_OR, I_XOR, I_AND, /* I(I, I) */
    I_SAR, I_SHR, I_SHL, /* I(I, ww) */

    I_STORED, /* (d, m) */
    I_STORES, /* (s, m) */
    I_STOREL, /* (l, m) */
    I_STOREW, /* (w, m) */
    I_STOREH, /* (w, m) */
    I_STOREB, /* (w, m) */

    I_LOADD, /* d(m) */
    I_LOADS, /* s(m) */
    I_LOADL, /* l(m) */
    I_LOADSW, I_LOADUW, /* I(mm) */
    I_LOADSH, I_LOADUH, /* I(mm) */
    I_LOADSB, I_LOADUB, /* I(mm) */

    I_BLIT, /* (m, m, w) */

    I_ALLOC4, /* m(l) */
    I_ALLOC8, /* m(l) */
    I_ALLOC16, /* m(l) */

    /* integer comparison: I(ws, ww) or I(ll, ll) */
    I_CEQW, I_CEQL, /* == */
    I_CNEW, I_CNEL, /* != */
    I_CSLEW, I_CSLEL, /* signed <= */
    I_CSLTW, I_CSLTL, /* signed < */
    I_CSGEW, I_CSGEL, /* signed >= */
    I_CSGTW, I_CSGTL, /* signed > */
    I_CULEW, I_CULEL, /* unsigned <= */
    I_CULTW, I_CULTL, /* unsigned < */
    I_CUGEW, I_CUGEL, /* unsigned >= */
    I_CUGTW, I_CUGTL, /* unsigned > */

    /* floating point comparison: I(ss, ss) or I(dd, dd) */
    I_CEQS, I_CEQD, /* == */
    I_CNES, I_CNED, /* != */
    I_CLES, I_CLED, /* <= */
    I_CLTS, I_CLTD, /* < */
    I_CGES, I_CGED, /* >= */
    I_CGTS, I_CGTD, /* > */
    I_COS, I_COD, /* ordered (no NaN) */
    I_CUOS, I_CUOD, /* unordered (has NaN) */

    I_EXTSW, I_EXTUW, /* l(w) */
    I_EXTSH, I_EXTUH, /* I(ww) */
    I_EXTSB, I_EXTUB, /* I(ww) */
    I_EXTS, /* d(s) */
    I_TRUNCD, /* s(d) */
    I_STOSI, /* I(ss) */
    I_STOUI, /* I(ss) */
    I_DTOSI, /* I(dd) */
    I_DTOUI, /* I(dd) */
    I_SWTOF, /* F(ww) */
    I_UWTOF, /* F(ww) */
    I_SLTOF, /* F(ll) */
    I_ULTOF, /* F(ll) */

    I_CAST, /* wlsd(sdwl) */
    I_COPY, /* T(T) */

    I_CALL,

    I_VASTART, /* (m) */
    I_VAARG, /* T(mmmm) */

    I_PHI,

    I_JMP, /* 'jmp' @IDENT */
    I_JNZ, /* 'jnz' VAL, @IDENT, @IDENT */
    I_RET, /* 'ret' [VAL] */
    I_HLT
  };
  uint8_t t;
  Type ret_t;
  Ident ident; /* optional */
  union {
    union {
      Value v;
      Ident ident;
    } arg[3];
    struct {
      Value f;
      uint16_t has_env_arg:1;
      uint16_t args_len:15; /* includes env and varargs */
      uint16_t has_vararg:1;
      uint16_t varargs_len:15;
      Value *args;
    } call;
    struct {
      uint16_t args_len;
      struct {
	Ident ident;
	Value v;
      } *args;
    } phi;
  } u;
  uint32_t next_id; /* idx into instr_pool; 0 means null */
} Instr;

typedef struct Block Block;
struct Block {
  Ident ident;
  uint32_t instr_id;
  uint16_t next_id; /* idx into blk_pool; 0 means null */
};

typedef struct FuncDef {
  Linkage linkage;
  Type ret_t;
  uint16_t params_len;
  uint16_t params_cap;
  Ident ident;
  struct {
    Type t;
    Ident ident;
  } *params;
  uint8_t is_varargs:1;
  uint8_t has_env_arg:1;
  uint16_t blk_id;
  uint16_t next_id; /* idx into func_def_pool; 0 means null */
} FuncDef;

/* ir.c */
Ident Ident_from_str(const char *);
const char *Ident_to_str(Ident);
void ir_cleanup(void);
