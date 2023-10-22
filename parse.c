#include <assert.h>
#include <ctype.h>
#include <string.h>

#include "all.h"

static FILE *input;

static int _getc(void) {
#if 0
  int c = fgetc(input);
  if (c == EOF) {
    printf(">> EOF\n");
  } else if (c == '\n') {
    printf(">> '\\n'\n");
  } else {
    printf(">> '%c'\n", c);
  }
  return c;
#else
  return fgetc(input);
#endif
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
  return strdup(buf);
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

void parse(FILE *_input) {
  Linkage linkage;
  input = _input;

 TAIL_CALL:
  skip_space_nl();
  switch (_peekc()) {
  case EOF: break;
  case 't': /* 'type' */
    expect_typedef();
    goto TAIL_CALL;
  default:
    (void)expect_linkage;
    (void)linkage;
    fail("funcdef / datadef parsing not implemented");
#if 0
    linkage = expect_linkage();
    skip_space();
#endif
    /* TODO: funcdef, datadef */
  }

  /* TODO: fix AgType size and log_align */
}
