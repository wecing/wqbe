#include <execinfo.h>
#include <stdarg.h>
#include <stdlib.h>

#include "all.h"

char *w_strdup(const char *s) {
    size_t sz = strlen(s);
    char *r = malloc(sz + 1);
    check(r != 0, "malloc failed");
    memcpy(r, s, sz+1);
    return r;
}

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
