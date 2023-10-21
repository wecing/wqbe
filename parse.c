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

static void expect_char(const char x) {
  char c = _getc();
  check(c == x, "char '%c' expected, got '%c'", x, c);
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
  c = _getc();
  check(!isalnum(c) && c != '_', "TYPE expected");
  if (c != EOF) _ungetc(c);
  return t;
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
 *
 * TODO: union
 */
static void expect_typedef(void) {
  uint8_t has_align = 0;
  int c;
  AgType *ag;
  Type tp;
  expect_keyword("type");
  skip_space();
  ag = AgType_get(AgType_lookup_or_alloc(expect_ident()));
  skip_space();
  expect_char('=');
  skip_space();
  c = _getc();
  if (c != EOF) _ungetc(c);
  if (c == 'a') {
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
  c = _getc();
  if (isdigit(c)) {
    _ungetc(c);
    check(has_align, "opaque type must have explicit align");
    ag->size = expect_number();
  } else {
    check(c != EOF, "incomplete TYPE");
    _ungetc(c);
    ag->has_body = 1;
    ag->body_len = 0;
    ag->body_cap = 4;
    ag->body = calloc(ag->body_cap, sizeof(ag->body[0]));
    c = ','; /* pretend there is a prefix ',' */
    while (c == ',') {
      /* handle ', }' (redundant comma) */
      skip_space();
      c = _getc();
      if (c != EOF) _ungetc(c);
      if (c == '}') break;

      skip_space();
      tp = expect_type();
      check(Type_is_subty(tp), "SUBTY expected");
      ag->body[ag->body_len].t = tp;
      ag->body[ag->body_len].count = 1;
      skip_space();
      c = _getc();
      if (c != EOF) _ungetc(c);
      if (isdigit(c)) {
        ag->body[ag->body_len].count = expect_number();
      }
      skip_space();
      c = _getc(); /* either ',' (continue) or '}' (break) */

      ag->body_len++;
      assert(ag->body_len > 0);
      if (ag->body_len == ag->body_cap) {
        ag->body_cap *= 2;
        assert(ag->body_len < ag->body_cap);
        ag->body = realloc(ag->body, sizeof(ag->body[0]) * ag->body_cap);
      }
    }
    if (c != EOF) _ungetc(c); /* unget '}' */
  }

  skip_space();
  expect_char('}');
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
  int c;
  Linkage r = {0};

 TAIL_CALL:
  c = _getc();
  switch (c) {
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
    c = _getc();
    if (c == '"') {
      _ungetc(c);
      r.sec_flags = expect_str();
    }
    skip_space_nl();
    goto TAIL_CALL;
  default:
    _ungetc(c);
    return r;
  }
}

void parse(FILE *_input) {
  int c;
  Linkage linkage;
  input = _input;

 TAIL_CALL:
  skip_space_nl();
  c = _getc();
  switch (c) {
  case EOF: break;
  case 't': /* 'type' */
    _ungetc('t');
    expect_typedef();
    goto TAIL_CALL;
  default:
    (void)expect_linkage;
    (void)linkage;
    fail("unexpected char '%c'", c);
#if 0
    _ungetc(c);
    linkage = expect_linkage();
    skip_space();
#endif
    /* TODO */
  }

  /* TODO: fix AgType size and log_align */
}
