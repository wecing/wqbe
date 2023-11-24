#include <assert.h>
#include <string.h>

#include "all.h"

static int dump_debug_info = 0;

static void dump_all(const char *prompt, ParseResult ir) {
    if (!dump_debug_info) return;
    if (prompt) {
        printf("\n####################\n");
        printf("### %s\n", prompt);
        printf("####################\n\n");
    }

    ir_dump_typedef();
    ir_dump_datadef(ir.first_datadef_id);
    ir_dump_funcdef(ir.first_funcdef_id);
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
    af = isel_simple_x64(fd);

    if (dump_debug_info) {
        printf("\n####################\n");
        printf("### %s after isel_simple_x64()\n", Ident_to_str(fd->ident));
        printf("####################\n\n");
    }
    dump_x64(af);

    /* TODO: reg alloc */
}

static void dump_usage(void) {
    printf("usage: wqbe [OPTIONS] [INPUT]\n");
    printf("    -d    dump debug info\n");
    printf("    -h    prints this messsage\n");
}

int main(int argc, char *argv[]) {
    int i;
    FILE *f = 0;
    ParseResult ir;

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
        } else {
            check(f == 0, "wqbe: multiple input specified");
            f = stdin;
            if (strcmp(argv[i], "-") != 0)
                f = fopen(argv[i], "r");
            check(f != 0, "wqbe: failed to open %s", argv[i]);
        }
    }

    if (f == 0) {
        fprintf(stderr,
                "wqbe: no input specified "
                "(use '-' for stdin input)\n\n");
        dump_usage();
        return 1;
    }

    ir = parse(f);
    if (f != stdin) fclose(f);
    dump_all("after parse()", ir);

    run_all_fd(ir.first_funcdef_id, dephi);
    dump_all("after dephi()", ir);

    run_all_fd(ir.first_funcdef_id, x64);

    ir_cleanup();
    return 0;
}
