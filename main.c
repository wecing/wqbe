#include <assert.h>

#include "all.h"

static void dump_all(const char *prompt, ParseResult ir) {
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

    printf("\n####################\n");
    printf("### %s after isel_simple_x64()\n",
           Ident_to_str(fd->ident));
    printf("####################\n\n");
    dump_x64(af);

    /* TODO: reg alloc */
}

int main(int argc, char *argv[]) {
    FILE *f;
    int need_close = 0;
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

    if (argc != 2) {
        fprintf(stderr, "usage: wqbe INPUT\n");
        return 1;
    }

    if (argv[1][0] == '-' && argv[1][1] == '\0') {
        f = stdin;
    } else {
        f = fopen(argv[1], "r");
        check(f != 0, "failed to open %s", argv[1]);
        need_close = 1;
    }
    ir = parse(f);
    if (need_close) fclose(f);
    dump_all("after parse()", ir);

    run_all_fd(ir.first_funcdef_id, dephi);
    dump_all("after dephi()", ir);

    run_all_fd(ir.first_funcdef_id, x64);

    ir_cleanup();
    return 0;
}
