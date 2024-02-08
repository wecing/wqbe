#include <assert.h>
#include <string.h>

#include "all.h"

static int dump_debug_info = 0;
static ParseResult ir;
static FILE *fout;
static int use_naive = 1; // TODO: turn off by default

static void dump_all(const char *prompt) {
    if (!dump_debug_info) return;
    if (prompt) {
        printf("####################\n");
        printf("### %s\n", prompt);
        printf("####################\n\n");
    }

    ir_dump_typedef();
    ir_dump_datadef(ir.first_datadef_id);
    ir_dump_funcdef(ir.first_funcdef_id);
    printf("\n");
}

static void run_all_fd(uint16_t id, void (*f)(FuncDef *)) {
    FuncDef *fd;
    while (id) {
        fd = FuncDef_get(id);
        f(fd);
        id = fd->next_id;
    }
}

static void x64(FuncDef *fd) {
    AsmFunc *af;

    if (use_naive) {
        af = isel_naive_x64(fd);
        if (dump_debug_info) {
            printf("####################\n");
            printf("### %s after isel_naive_x64()\n", Ident_to_str(fd->ident));
            printf("####################\n\n");
            dump_x64(af, fd->linkage, stdout);
            printf("\n");
        }

        af = ra_naive_x64(af, &ir.first_datadef_id);
        if (dump_debug_info) {
            printf("####################\n");
            printf("### %s after ra_naive_x64()\n", Ident_to_str(fd->ident));
            printf("####################\n\n");
        }
        dump_x64(af, fd->linkage, fout);
    } else {
        af = isel_x64(fd);
        if (dump_debug_info) {
            printf("####################\n");
            printf("### %s after isel_x64()\n", Ident_to_str(fd->ident));
            printf("####################\n\n");
            dump_x64(af, fd->linkage, stdout);
            printf("\n");
        }

        // TODO: rest of the pipeline
    }
}

static void run_all_dd(uint16_t id, void (*f)(DataDef, FILE *)) {
    DataDef dd;
    while (id) {
        dd = *DataDef_get(id);
        f(dd, fout);
        id = dd.next_id;
    }
}

static void emit_dbgfile(uint16_t id, const char *s) {
    fprintf(fout, ".file %u \"%s\"\n", id, s);
}

static void dump_usage(void) {
    printf("usage: wqbe [OPTIONS] [INPUT]\n");
    printf("    -d          dump debug info\n");
    printf("    -h          prints this messsage\n");
    printf("    -o file     output to file\n");
    printf("    --naive     use simpler naive codegen\n");
}

int main(int argc, char *argv[]) {
    int i;
    FILE *f = 0;
    char *f_path = 0, *fout_path = 0;
    fout = stdout;

    assert(sizeof(Type) == 4);
    assert(sizeof(ArrType) == 8);
    assert(sizeof(AgType) == 16);
    assert(sizeof(DataDef) == 40);
    assert(sizeof(Block) == 16);
    assert(sizeof(FuncDef) == 48);
    assert(sizeof(Instr) == 48);
    assert(sizeof(AsmInstr) == 24);
    assert(sizeof(((AsmFunc *) 0)->label[0]) == 8);

    for (i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            dump_usage();
            return 0;
        } else if (strcmp(argv[i], "-d") == 0) {
            dump_debug_info = 1;
        } else if (strcmp(argv[i], "-o") == 0) {
            check(i + 1 < argc, "wqbe: no output file specified for -o");
            i++;
            check(fout_path == 0,
                  "wqbe: multiple output file specified: %s and %s",
                  fout_path, argv[i]);
            if (strcmp(argv[i], "-") != 0) {
                fout = fopen(argv[i], "w");
                check(fout != 0, "wqbe: failed to open %s", argv[i]);
                fout_path = argv[i];
            }
        } else if (strcmp(argv[i], "-t") == 0) {
            check(i + 1 < argc, "wqbe: no output file specified for -o");
            i++;
            check(strcmp(argv[i], "amd64_sysv") == 0,
                  "unsupported target %s", argv[i]);
        } else if (strcmp(argv[i], "--naive") == 0) {
            use_naive = 1;
        } else {
            check(argv[i][0] != '-' || argv[i][1] == '\0',
                  "unrecognized parameter %s", argv[i]);
            check(f_path == 0, "wqbe: multiple input specified: %s and %s",
                  f_path, argv[i]);
            f = stdin;
            if (strcmp(argv[i], "-") != 0)
                f = fopen(argv[i], "r");
            check(f != 0, "wqbe: failed to open %s", argv[i]);
            f_path = argv[i];
        }
    }

    /* this is QBE's behavior. */
    if (f_path == 0)
        f = stdin;

    ir = parse(f);
    if (f != stdin) fclose(f);
    dump_all("after parse()");

    run_all_fd(ir.first_funcdef_id, dephi);
    dump_all("after dephi()");

    /* emit .file assembler directives.
       note: current impl is a hack that only works for FUNCDEF. */
    ir_foreach_dbgfile(emit_dbgfile);
    fprintf(fout, ".file \"\"\n\n"); /* reset .file */

    run_all_fd(ir.first_funcdef_id, x64);
    run_all_dd(ir.first_datadef_id, dump_x64_data);

    if (fout != stdout) fclose(fout);

    ir_cleanup();
    return 0;
}
