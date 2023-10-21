#include <stdarg.h>

#include "all.h"

void check(int cond, const char *msg, ...) {
  va_list args;
  if (cond) return;
  va_start(args, msg);
  vfprintf(stderr, msg, args);
  fputc('\n', stderr);
  va_end(args);
  exit(1);
}

void fail(const char *msg, ...) {
  va_list args;
  va_start(args, msg);
  vfprintf(stderr, msg, args);
  fputc('\n', stderr);
  va_end(args);
  exit(1);
}
