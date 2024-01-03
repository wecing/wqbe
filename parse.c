#include <assert.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"

static FILE *input;

static int _getc(void) {
    return fgetc(input);
}

static void _ungetc(int c) {
    assert(c != EOF);
    ungetc(c, input);
}

static int _peekc(void) {
    int c = fgetc(input);
    if (c != EOF) ungetc(c, input);
    return c;
}

static void skip_space(void) {
    int c;
    do { c = _getc(); } while (isspace(c) && c != '\n');
    if (c == '#') {
        do { c = _getc(); } while (c != '\n' && c != EOF);
    }
    if (c != EOF) _ungetc(c); /* unget first non space (may be \n) */
}

static void skip_space_nl(void) {
    int c;
TAIL_CALL:
    do { c = _getc(); } while (isspace(c));
    switch (c) {
    case EOF: return;
    case '#':
        do { c = _getc(); } while (c != '\n' && c != EOF);
        if (c == EOF) return;
        goto TAIL_CALL;
    }
    _ungetc(c);
}

static void expect_char(const char ex) {
    int c = _getc();
    if (c == ex) return;
    if (c == EOF) fail("char '%c' expected, got EOF", ex);
    fail("char '%c' expected, got '%c'", ex, c);
}

static void expect_space_nl(void) {
    skip_space();
    expect_char('\n');
    skip_space_nl(); /* NL could actually have multiple '\n' */
}

static uint64_t expect_number(void) {
    int c;
    uint64_t r = 0;
    c = _getc();
    while (isdigit(c)) {
        r = r * 10 + c - '0';
        c = _getc();
    }
    if (c != EOF) _ungetc(c);
    return r;
}

/* string literal, '"' ... '"' */
static char* expect_str(void) {
    int c, i = 0;
    char buf[1024];
    c = _getc();
    check(c == '"', "string literal expected, got '%c'", c);
    c = _getc();
    while (c != '"') {
        check(c != EOF, "string literal not closed");
        buf[i++] = c;
        assert((uint64_t) i < sizeof(buf));
        c = _getc();
    }
    buf[i] = '\0';
    return w_strdup(buf);
}

static void expect_keyword(const char *s) {
    int c;
    const char *p = s;

    do {
        c = _getc();
    } while (c == *p++);
    p--;

    check(*p == '\0' && !isalnum(c), "keyword '%s' expected", s);
}

static Ident expect_ident(void) {
    int c, i = 0;
    char buf[1024];
    c = _getc();
    check(c == ':' || c == '$' || c == '%' || c == '@', "IDENT expected");
    buf[i++] = c;
    c = _getc();
    while (isalnum(c) || c == '_' || c == '.') {
        assert((uint64_t) i < sizeof(buf));
        buf[i++] = c;
        c = _getc();
    }
    if (c != EOF) _ungetc(c);
    assert((uint64_t) i < sizeof(buf));
    buf[i] = '\0';
    return Ident_from_str(buf);
}

static Type expect_type(void) {
    int c;
    Type t = {0};
    c = _getc();
    check(c != EOF, "TYPE expected, got EOF");
    switch (c) {
    case ':':
        _ungetc(':');
        return AgType_lookup_or_alloc(expect_ident());
    case 'w': t.t = TP_W; break;
    case 'l': t.t = TP_L; break;
    case 'd': t.t = TP_D; break;
    case 'b': t.t = TP_B; break;
    case 'h': t.t = TP_H; break;
    case 's': /* s, sb, sh */
        c = _getc();
        switch (c) {
        case 'b': t.t = TP_SB; break;
        case 'h': t.t = TP_SH; break;
        default:
            if (c != EOF) _ungetc(c);
            t.t = TP_S;
        }
        break;
    case 'u': /* ub, uh */
        c = _getc();
        switch (c) {
        case 'b': t.t = TP_UB; break;
        case 'h': t.t = TP_UH; break;
        default:
            fail("TYPE expected, got 'u%c'", c);
            return t; /* unreachable */
        }
        break;
    default:
        fail("TYPE expected, got '%c'", c);
        return t; /* unreachable */
    }

    /*
     * check for illegal type names, e.g.
     * - sai
     * - 's_' FP
     * - 'd_' FP
     */
    c = _peekc();
    check(!isalnum(c) && c != '_', "TYPE expected");
    return t;
}

/*
 * expects '{' ( SUBTY [NUMBER] ), '}'
 *
 * the '{' will be omitted if expect_lbrace == 0.
 */
static ArrType *expect_struct_body(int expect_lbrace) {
    int c;
    ArrType *sb;
    int sb_len = 0, sb_cap = 4;
    sb = malloc(sizeof(sb[0]) * sb_cap);

    if (expect_lbrace) expect_char('{');
    c = ',';
    while (c != '}') {
        skip_space();
        c = _peekc();
        if (c == '}') {
            c = _getc();
            break; /* redundant comma ',}' or empty body '{}' */
        }

        if (sb_len == sb_cap - 1) {
            sb_cap += 4;
            sb = realloc(sb, sizeof(sb[0]) * sb_cap);
        }

        sb[sb_len].t = expect_type();
        sb[sb_len].count = 1;
        check(Type_is_subty(sb[sb_len].t), "SUBTY expected");
        skip_space();
        if (isdigit(_peekc())) {
            sb[sb_len].count = expect_number();
        }
        skip_space();
        c = _getc();
        check(c == ',' || c == '}', "expected ',' or '}'");

        sb_len++;
    }

    sb[sb_len].t.t = TP_UNKNOWN;
    sb[sb_len].t.ag_id = 0;
    sb[sb_len].count = 0;
    return sb;
}

/*
 * TYPEDEF :=
 *     # Regular type
 *     'type' :IDENT '=' ['align' NUMBER]
 *     '{'
 *         ( SUBTY [NUMBER] ),
 *     '}'
 *   | # Opaque type
 *     'type' :IDENT '=' 'align' NUMBER '{' NUMBER '}'
 *   | # Union type (not documented)
 *     'type' :IDENT '=' ['align' NUMBER]
 *     '{'
 *         ( '{'
 *             ( SUBTY [NUMBER] ),
 *         '}' )+
 *     '}'
 */
static void expect_typedef(void) {
    uint8_t has_align = 0;
    int c;
    AgType *ag;
    int ub_len;
    int ub_cap;
    expect_keyword("type");
    skip_space();
    ag = AgType_get(AgType_lookup_or_alloc(expect_ident()));
    skip_space();
    expect_char('=');
    skip_space();
    ag->log_align = 0x7;
    if (_peekc() == 'a') {
        expect_keyword("align");
        has_align = 1;
        switch (expect_number()) {
#define F(n) case (1 << n): ag->log_align = n; break
            /* align  1 => log_align = 0
               align 16 => log_align = 4 */
            F(0); F(1); F(2); F(3); F(4);
#undef F
        default:
            fail("unsupported alignment");
            return; /* unreachable */
        }
    }
    skip_space();
    expect_char('{');

    skip_space();
    c = _peekc();
    if (isdigit(c)) {
        check(has_align, "opaque type must have explicit align");
        ag->is_opaque = 1;
        ag->size = expect_number();
        skip_space();
        expect_char('}');
    } else if (c == '{') {
        ag->is_union = 1;
        ub_len = 0;
        ub_cap = 4;
        ag->u.ub = malloc(sizeof(ArrType *) * ub_cap);
        while (c == '{') {
            ag->u.ub[ub_len++] = expect_struct_body(/*expect_lbrace=*/1);
            if (ub_len == ub_cap - 1) {
                ub_cap *= 2;
                assert(ub_len < ub_cap - 1);
                ag->u.ub = realloc(ag->u.ub, sizeof(ArrType *) * ub_cap);
            }
            skip_space();
            c = _peekc(); /* inner '{', or outer '}' */
            check(c != EOF, "incomplete union definition");
            check(c == '{' || c == '}',
                  "unexpected char '%c' in union definition", c);
        }
        ag->u.ub[ub_len] = 0;
        skip_space();
        expect_char('}'); /* outer '}' */
    } else {
        check(c != EOF, "incomplete TYPE");
        ag->u.sb = expect_struct_body(/*expect_lbrace=*/0);
    }
}

/*
 * LINKAGE :=
 *     'export' [NL]
 *   | 'thread' [NL]
 *   | 'section' SECNAME [NL]
 *   | 'section' SECNAME SECFLAGS [NL]
 *
 * This function parses LINKAGE* (zero or more LINKAGE).
 */
static Linkage expect_linkage(void) {
    Linkage r = {0};

TAIL_CALL:
    switch (_peekc()) {
    case EOF: return r;
    case 'e':
        expect_keyword("export");
        r.is_export = 1;
        skip_space_nl();
        goto TAIL_CALL;
    case 't':
        expect_keyword("thread");
        r.is_thread = 1;
        skip_space_nl();
        goto TAIL_CALL;
    case 's':
        expect_keyword("section");
        r.is_section = 1;
        if (r.sec_name) free(r.sec_name);
        if (r.sec_flags) free(r.sec_flags);
        r.sec_name = 0;
        r.sec_flags = 0;
        skip_space();
        r.sec_name = expect_str();
        skip_space();
        if (_peekc() == '"') {
            r.sec_flags = expect_str();
        }
        skip_space_nl();
        goto TAIL_CALL;
    default:
        return r;
    }
}

/*
 * f32: 's_' FP
 * f64: 'd_' FP
 */
static double expect_fp(int is_f32) {
    int c;
    int i = 0;
    char buf[30];
    float f;
    double d;
    int n = 0;
    c = _getc();
    check(c == 's' || c == 'd', "FP should begin with 's_' or 'd_'");
    expect_char('_');
    c = _getc();
    while (i < (int) sizeof(buf)
           && (isalnum(c) || c == '.' || c == '+' || c == '-')) {
        buf[i++] = c;
        c = _getc();
    }
    if (c != EOF) _ungetc(c);
    assert(i < (int) sizeof(buf));
    buf[i] = '\0';
    if (is_f32) {
        sscanf(buf, "%f%n", &f, &n);
        check(n > 0 && n == i, "illegal FP: s_%s", buf);
        return (double) f;
    } else {
        sscanf(buf, "%lf%n", &d, &n);
        check(n > 0 && n == i, "illegal FP: d_%s; n=%d, i=%d", buf, n, i);
        return d;
    }
}

/*
 * VALUE := DYNCONST | %IDENT
 * DYNCONST := CONST | 'thread' $IDENT
 * CONST := ['-'] NUMBER | 's_' FP | 'd_' FP | $IDENT
 */
static Value expect_value(void) {
    Value v = {0};
    switch (_peekc()) {
    case '%':
        v.t = V_TMP;
        v.u.tmp_ident = expect_ident();
        break;
    case 't':
        expect_keyword("thread");
        skip_space();
        check(_peekc() == '$', "$IDENT expected for thread-local symbol");
        v.t = V_CTHS;
        v.u.thread_ident = expect_ident();
        break;
    case '-':
        _getc();
        v.t = V_CI;
        v.u.u64 = (uint64_t) (-(int64_t) expect_number());
        break;
    case '0': case '1': case '2': case '3': case '4':
    case '5': case '6': case '7': case '8': case '9':
        v.t = V_CI;
        v.u.u64 = expect_number();
        break;
    case 's':
        v.t = V_CS;
        v.u.s = (float) expect_fp(/*is_f32=*/1);
        break;
    case 'd':
        v.t = V_CD;
        v.u.d = expect_fp(/*is_f32=*/0);
        break;
    case '$':
        v.t = V_CSYM;
        v.u.global_ident = expect_ident();
        break;
    case EOF:
        fail("VALUE expected, got EOF");
        break; /* unreachable */
    default:
        fail("VALUE expected, got '%c'", _peekc());
    }
    return v;
}

static Value expect_const(void) {
    Value v = expect_value();
    check(v.t == V_CI || v.t == V_CS || v.t == V_CD || v.t == V_CSYM,
          "CONST expected, got value type %d", v.t);
    return v;
}

/*
 * DATAITEM :=
 *     $IDENT ['+' NUMBER]  # Symbol and offset
 *   |  '"' ... '"'         # String
 *   |  CONST               # Constant
 */
static DataItem expect_dataitem_single(void) {
    DataItem di;
    switch (_peekc()) {
    case '$':
        di.t = DI_SYM_OFF;
        di.u.sym_off.ident = expect_ident();
        di.u.sym_off.offset = 0;
        skip_space();
        if (_peekc() == '+') {
            expect_char('+');
            skip_space();
            di.u.sym_off.offset = expect_number();
        }
        return di;
    case '"':
        di.t = DI_STR;
        di.u.str = expect_str();
        return di;
    default:
        di.t = DI_CONST;
        di.u.cst = expect_const();
        return di;
    }
}

/* expects DATAITEM+, terminated with ',' or '}' */
static DataItem *expect_dataitem_rep(void) {
    int c;
    int i = 0, cap = 2;
    DataItem *di;
    di = malloc(sizeof(di[0]) * cap);
    di[i++] = expect_dataitem_single();
    skip_space();
    while (1) {
        c = _peekc();
        if (c == ',' || c == '}') break;
        di[i++] = expect_dataitem_single();
        skip_space();
        if (i == cap) {
            cap += 4;
            di = realloc(di, sizeof(di[0]) * cap);
        }
    }
    assert(i < cap);
    di[i].t = DI_UNKNOWN;
    return di;
}

/* expects '{' ( EXTTY DATAITEM+ | 'z' NUMBER ), '}' */
static DataDefItem *expect_datadef_body(void) {
    int c;
    int i = 0, cap = 4;
    DataDefItem *ddi;
    ddi = malloc(sizeof(ddi[0]) * cap);
    expect_char('{');
    skip_space();
    while ((c = _peekc()) != '}') {
        check(c != EOF, "DATADEF body incomplete");
        ddi[i].is_dummy_item = 0;
        if (c == 'z') {
            expect_keyword("z");
            skip_space();
            ddi[i].is_ext_ty = 0;
            ddi[i].u.zero_size = expect_number();
        } else {
            ddi[i].is_ext_ty = 1;
            ddi[i].u.ext_ty.t = expect_type();
            check(Type_is_extty(ddi[i].u.ext_ty.t),
                  "EXTTY expected in DATADEF body");
            skip_space();
            ddi[i].u.ext_ty.items = expect_dataitem_rep();
        }

        i++;
        if (i == cap) {
            cap += 4;
            ddi = realloc(ddi, sizeof(ddi[0]) * cap);
        }

        skip_space();
        c = _peekc();
        if (c == ',') {
            _getc();
            skip_space();
        } else {
            check(c == '}', "',' or '}' expected in DATADEF body");
        }
    }
    assert(_getc() == '}');
    assert(i < cap);
    ddi[i].is_dummy_item = 1;
    return ddi;
}

/*
 * DATADEF :=
 *     LINKAGE*
 *     'data' $IDENT '=' ['align' NUMBER]
 *     '{'
 *         ( EXTTY DATAITEM+
 *         | 'z'   NUMBER ),
 *     '}'
 */
static uint16_t expect_datadef(Linkage linkage) {
    uint16_t dd_id;
    DataDef *dd;

    expect_keyword("data");
    skip_space();
    check(_peekc() == '$', "$IDENT expected");
    dd_id = DataDef_alloc(expect_ident());
    dd = DataDef_get(dd_id);
    dd->linkage = linkage;
    skip_space();
    expect_char('=');
    skip_space();
    dd->log_align = 0xFF; /* not specified */
    if (_peekc() == 'a') {
        expect_keyword("align");
        skip_space();
        switch (expect_number()) {
#define F(n) case (1 << n): dd->log_align = n; break
            /* align  1 => log_align = 0
               align 16 => log_align = 4 */
            F(0); F(1); F(2); F(3); F(4);
#undef F
        default:
            fail("unsupported alignment");
            return 0; /* unreachable */
        }
    }
    skip_space();
    dd->items = expect_datadef_body();
    return dd_id;
}

/*
 * expects '(' (PARAM), ')'
 *
 * PARAM :=
 *     ABITY %IDENT  # Regular parameter
 *   | 'env' %IDENT  # Environment parameter (first)
 *   | '...'         # Variadic marker (last)
 */
static void expect_funcdef_params(FuncDef *fd) {
    int i = 0, cap = 2;
    int c = '\0'; /* \0: marker for first param */
    fd->params = malloc(sizeof(fd->params[0]) * cap);
    fd->is_varargs = 0;
    expect_char('(');
    skip_space();
    if (_peekc() == ')') c = _getc(); /* '(' ')' */
    while (c != ')') {
        check(!fd->is_varargs, "no params expected after '...'");
        skip_space();
        if (_peekc() == 'e') {
            check(c == '\0', "only the first param could be 'env'");
            expect_keyword("env");
            skip_space();
            check(_peekc() == '%', "%IDENT expected");
            fd->params[i].t.t = TP_NONE;
            fd->params[i].ident = expect_ident();
            i++;
        } else if (_peekc() == '.') {
            check(_getc() && _peekc() == '.' &&
                  _getc() && _peekc() == '.' &&
                  _getc() && _peekc() != '.',
                  "'...' expected");
            fd->is_varargs = 1;
        } else {
            fd->params[i].t = expect_type();
            skip_space();
            check(Type_is_abity(fd->params[i].t), "ABITY expected");
            check(_peekc() == '%', "%IDENT expected");
            fd->params[i].ident = expect_ident();
            i++;
        }
        skip_space();

        if (i == cap) {
            cap += 2;
            fd->params = realloc(fd->params, sizeof(fd->params[0]) * cap);
        }

        c = _getc();
        check(c == ',' || c == ')', "',' or ')' expected in params list");
        /* no redundant comma ',)' */
    }
    fd->params[i].t.t = TP_UNKNOWN;
}

static uint8_t expect_instr_name(void) {
    static const uint8_t t[] = {
#define I(up,low) I_##up,
#include "instr.inc"
#undef I
        0
    };
    static const char *s[] = {
#define I(up,low) #low,
#include "instr.inc"
#undef I
        0
    };
    int x = 0, y = countof(t) - 2; /* inclusive */
    int i = 0;
    char buf[10];
    int c, cmp;

    c = _getc();
    while (isalnum(c) && i < (int) countof(buf) - 1) {
        buf[i++] = c;
        c = _getc();
    }
    buf[i] = '\0';
    check(c == EOF || isspace(c), "unrecognized op: '%s%c...'", buf, c);
    if (c != EOF) _ungetc(c);

    while (x <= y) {
        i = (x + y) / 2;
        cmp = strcmp(buf, s[i]);
        if (cmp == 0) {
            return t[i];
        } else if (cmp < 0) {
            y = i - 1;
        } else {
            x = i + 1;
        }
    }
    fail("unrecognized op: '%s'", buf);
    return I_UNKNOWN; /* unreachable */
}

/*
 * expects '(' (ARG), ')'
 *
 * ARG :=
 *     ABITY VAL  # Regular argument
 *   | 'env' VAL  # Environment argument (first)
 *   | '...'      # Variadic marker
 */
static void expect_call_args(Instr *p) {
    int c = '(';
    int i = 0, cap = 4;

    p->u.call.args = malloc(sizeof(p->u.call.args[0]) * cap);
    p->u.call.va_begin_idx = 0xFFFF;
    expect_char('(');
    skip_space();
    if (_peekc() == ')') c = _getc();
    while (c == '(' || c == ',') {
        skip_space();
        if (_peekc() == 'e' && i == 0) {
            expect_keyword("env");
            skip_space();
            p->u.call.args[i].t.t = TP_NONE;
            p->u.call.args[i].v = expect_value();
            i++;
        } else if (_peekc() == '.') {
            check(_getc() && _peekc() == '.' &&
                  _getc() && _peekc() == '.' &&
                  _getc() && _peekc() != '.',
                  "variadic marker '...' expected");
            p->u.call.va_begin_idx = i;
            /* no i++ */
        } else {
            p->u.call.args[i].t = expect_type();
            check(Type_is_abity(p->u.call.args[i].t), "ABITY expected");
            skip_space();
            p->u.call.args[i].v = expect_value();
            i++;
        }

        if (i == cap) {
            cap += 4;
            p->u.call.args = realloc(p->u.call.args,
                                     sizeof(p->u.call.args[0]) * cap);
        }

        skip_space();
        c = _getc();
    }
    p->u.call.args[i].t.t = TP_UNKNOWN;
    check(c == ')', "ARG list must be termined by ')'");
    return;
}

/*
 * expects (PHI | INST | JUMP) NL
 *
 * CALL := [%IDENT '=' ABITY] 'call' VAL '(' (ARG), ')'
 * PHI := %IDENT '=' BASETY 'phi' ( @IDENT VAL ),
 *
 * other instructions, except JUMP and BLIT:
 *
 * [%IDENT '=' ABITY] OPNAME VAL [, VAL]
 */
static uint32_t expect_instr(void) {
    uint32_t id;
    Instr *p;
    int i, args_cap;
    int c;

    id = Instr_alloc();
    p = Instr_get(id);
    if (_peekc() == '%') {
        p->ident = expect_ident();
        skip_space();
        expect_char('=');
        skip_space();
        p->ret_t = expect_type();
        check(Type_is_abity(p->ret_t), "ABITY expected for instr return type");
        skip_space();
    } else {
        p->ret_t.t = TP_NONE;
    }
    p->t = expect_instr_name();
    skip_space();
    switch (p->t) {
    case I_CALL:
        p->u.call.f = expect_value();
        skip_space();
        expect_call_args(p);
        break;
    case I_PHI:
        i = 0;
        args_cap = 4;
        p->u.phi.args = malloc(sizeof(p->u.phi.args[0]) * args_cap);
        c = ',';
        while (c == ',') {
            skip_space();
            check(_peekc() == '@', "@IDENT expected");
            p->u.phi.args[i].ident = expect_ident();
            skip_space();
            p->u.phi.args[i].v = expect_value();

            i++;
            if (i == args_cap) {
                args_cap += 4;
                p->u.phi.args = realloc(p->u.phi.args,
                                        sizeof(p->u.phi.args[0]) * args_cap);
            }

            skip_space();
            c = _peekc();
            if (c == ',') {
                _getc();
            }
        }
        p->u.phi.args[i].v.t = V_UNKNOWN;
        break;
    case I_JMP:
        check(_peekc() == '@', "@IDENT expected for jmp");
        p->u.jump.dst = expect_ident();
        break;
    case I_JNZ:
        p->u.jump.v = expect_value();
        skip_space(); expect_char(','); skip_space();
        check(_peekc() == '@', "@IDENT expected for jnz");
        p->u.jump.dst = expect_ident();
        skip_space(); expect_char(','); skip_space();
        check(_peekc() == '@', "@IDENT expected for jnz");
        p->u.jump.dst_else = expect_ident();
        break;
    case I_RET:
        if (_peekc() != '\n') {
            p->u.jump.v = expect_value();
        } else {
            p->u.jump.v.t = V_UNKNOWN;
        }
        break;
    case I_HLT:
        break;
    case I_BLIT:
        p->u.args[0] = expect_value();
        skip_space(); expect_char(','); skip_space();
        p->u.args[1] = expect_value();
        skip_space(); expect_char(','); skip_space();
        p->blit_sz = expect_number();
        break;
    default:
        p->u.args[0] = expect_value();
        skip_space();
        if (_peekc() == ',') {
            _getc();
            skip_space();
            p->u.args[1] = expect_value();
        }
    }

    if (p->t == I_LOAD) {
        switch (p->ret_t.t) {
        case TP_W: p->t = I_LOADSW; break;
        case TP_L: p->t = I_LOADL; break;
        case TP_S: p->t = I_LOADS; break;
        case TP_D: p->t = I_LOADD; break;
        default:
            fail("ambigous LOAD instruction: ret_t.t = %d", p->ret_t.t);
        }
    }

    expect_space_nl();
    return id;
}

/*
 * BLOCK :=
 *     @IDENT NL     # Block label
 *     ( PHI NL )*   # Phi instructions
 *     ( INST NL )*  # Regular instructions
 *     JUMP NL       # Jump or return
 *
 * The last JUMP is actually optional.
 */
static uint16_t expect_block(void) {
    uint16_t blk_id;
    Block *blk;
    uint32_t instr_id, last_instr_id = 0;
    Instr *instr;
    int seen_non_phi = 0;
    int seen_jump = 0;

    blk_id = Block_alloc();
    blk = Block_get(blk_id);
    check(_peekc() == '@', "@IDENT expected for BLOCK");
    blk->ident = expect_ident();
    blk->instr_id = 0;
    blk->jump_id = 0;
    expect_space_nl();
    while (_peekc() != '@' && _peekc() != '}') {
        check(!seen_jump, "at most one JUMP expected in BLOCK");
        instr_id = expect_instr();
        instr = Instr_get(instr_id);
        switch (instr->t) {
        case I_PHI:
            check(!seen_non_phi, "PHI must only appear at beginning of BLOCK");
            if (!blk->instr_id)
                blk->instr_id = instr_id;
            else
                Instr_get(last_instr_id)->next_id = instr_id;
            break;
        case I_JMP: case I_JNZ: case I_RET: case I_HLT:
            seen_non_phi = 1;
            seen_jump = 1;
            blk->jump_id = instr_id;
            break;
        default:
            if (!blk->instr_id)
                blk->instr_id = instr_id;
            else
                Instr_get(last_instr_id)->next_id = instr_id;
            seen_non_phi = 1;
        }
        last_instr_id = instr_id; /* JUMP instr's next_id won't be set */
    }
    return blk_id;
}

/*
 * FUNCDEF :=
 *     LINKAGE*
 *     'function' [ABITY] $IDENT '(' (PARAM), ')' [NL]
 *     '{' NL
 *         BLOCK+
 *     '}'
 */
static uint16_t expect_funcdef(Linkage linkage) {
    uint16_t id, blk_id, next_blk_id;
    FuncDef *fd;
    Type tp;
    Block *blk;
    Instr *instr;
    expect_keyword("function");
    skip_space();
    if (_peekc() != '$') {
        tp = expect_type();
        skip_space();
        check(Type_is_abity(tp), "[ABITY] expected for FUNCDEF return type");
    } else {
        tp.t = TP_NONE;
    }
    id = FuncDef_alloc(expect_ident());
    fd = FuncDef_get(id);
    fd->linkage = linkage;
    fd->ret_t = tp;
    expect_funcdef_params(fd);
    skip_space_nl();
    expect_char('{');
    expect_space_nl();
    check(_peekc() == '@', "@IDENT NL expected");
    blk_id = expect_block();
    fd->blk_id = blk_id;
    while (_peekc() == '@') {
        Block_get(blk_id)->next_id = next_blk_id = expect_block();
        blk_id = next_blk_id;
    }
    expect_char('}');
    Block_get(blk_id)->next_id = 0;

    /* fix Block implicit jmp */
    blk_id = fd->blk_id;
    while (blk_id != 0) {
        blk = Block_get(blk_id);
        if (blk->jump_id == 0) {
            check(blk->next_id != 0, "implicit jump with no successor");
            blk->jump_id = Instr_alloc();
            instr = Instr_get(blk->jump_id);
            instr->t = I_JMP;
            instr->ret_t.t = TP_UNKNOWN;
            instr->u.jump.dst = Block_get(blk->next_id)->ident;
        }
        blk_id = blk->next_id;
    }
    return id;
}

ParseResult parse(FILE *_input) {
    ParseResult r = {0};
    uint16_t cur_dd = 0, dd = 0;
    uint16_t cur_fd = 0, fd = 0;
    Linkage linkage;
    int c1, c2;
    input = _input;

TAIL_CALL:
    skip_space_nl();
    switch (c1 = _peekc()) {
    case EOF: break;
    case 't': /* 'type' | 'thread' */
    case 'd': /* 'data' | 'dbgfile' */
        _getc();
        c2 = _peekc();
        _ungetc(c1);
        if (c1 == 't' && c2 == 'y') { /* 'type' */
            expect_typedef();
            goto TAIL_CALL;
        } else if (c1 == 'd' && c2 == 'b') { /* 'dbgfile' */
            /* note: we cannot support dbgfile since we currently loads the
               whole IL file without preserving original DATADEF/FUNCDEF
               orderings. */
            expect_keyword("dbgfile");
            free(expect_str());
            goto TAIL_CALL;
        }
        /* fallthrough */
    default:
        linkage = expect_linkage();
        skip_space();
        switch (_peekc()) {
        case 'd': /* 'data' */
            dd = expect_datadef(linkage);
            if (cur_dd) {
                DataDef_get(cur_dd)->next_id = dd;
            } else {
                r.first_datadef_id = dd;
            }
            cur_dd = dd;
            goto TAIL_CALL;
        case 'f': /* 'function' */
            fd = expect_funcdef(linkage);
            if (cur_fd) {
                FuncDef_get(cur_fd)->next_id = fd;
            } else {
                r.first_funcdef_id = fd;
            }
            cur_fd = fd;
            goto TAIL_CALL;
        default:
            fail("unexpected global definition");
        }
    }

    ir_fix_typedef_size_align();
    return r;
}
