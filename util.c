#include <execinfo.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"

void check(int cond, const char *msg, ...) {
    va_list args;
    if (cond) return;
    va_start(args, msg);
    vfprintf(stderr, msg, args);
    fputc('\n', stderr);
    va_end(args);
    dump_stacktrace();
    exit(1);
}

void fail(const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    vfprintf(stderr, msg, args);
    fputc('\n', stderr);
    va_end(args);
    dump_stacktrace();
    exit(1);
}

void dump_stacktrace(void) {
    void* callstack[128];
    int i, frames = backtrace(callstack, 128);
    char** strs = backtrace_symbols(callstack, frames);
    printf("\nstacktrace:\n");
    for (i = 0; i < frames; ++i) {
        printf("    %s\n", strs[i]);
    }
    free(strs);
}

char *w_strdup(const char *s) {
    size_t sz = strlen(s);
    char *r = malloc(sz + 1);
    check(r != 0, "malloc failed");
    memcpy(r, s, sz+1);
    return r;
}

int w_snprintf(char *buf, size_t sz, const char *fmt, ...) {
    int r;
    va_list args;
    va_start(args, fmt);
#if defined(__linux__) && !defined(__USE_ISOC99)
    /* linux stdio.h hides (v)snprintf under C89. */
    (void) sz;
    r = vsprintf(buf, fmt, args);
#else
    r = vsnprintf(buf, sz, fmt, args);
#endif
    va_end(args);
    return r;
}
