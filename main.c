#include <assert.h>

#include "all.h"

int main(int argc, char *argv[]) {
    FILE *f;
    int need_close = 0;
    ParseResult ir;

    assert(sizeof(Type) == 4);
    assert(sizeof(ArrType) == 8);
    assert(sizeof(AgType) == 16);
    assert(sizeof(DataDef) == 40);
    assert(sizeof(Block) == 12);
    assert(sizeof(FuncDef) == 56);
    assert(sizeof(Instr) == 72);

    if (argc != 2) {
        fprintf(stderr, "usage: wqbe INPUT\n");
        return 1;
    }

    if (argv[1][0] == '-' && argv[1][1] == '\0') {
        f = stdin;
    } else {
        f = fopen(argv[1], "r");
        need_close = 1;
    }

    ir = parse(f);

    if (need_close) fclose(f);

    ir_dump_typedef();
    ir_dump_datadef(ir.first_datadef_id);

    ir_cleanup();
    return 0;
}
