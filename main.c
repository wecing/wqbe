#include <assert.h>

#include "all.h"

int main(int argc, char *argv[]) {
  FILE *f;

  assert(sizeof(Type) == 4);
  assert(sizeof(ArrType) == 8);
  assert(sizeof(AgType) == 16);
  assert(sizeof(DataDef) == 48);
  assert(sizeof(Block) == 12);
  assert(sizeof(FuncDef) == 56);
  assert(sizeof(Instr) == 72);

  if (argc != 2) {
    fprintf(stderr, "usage: wqbe INPUT\n");
    return 1;
  }

  if (argv[1][0] == '-' && argv[1][1] == '\0') {
    parse(stdin);
  } else {
    f = fopen(argv[1], "r");
    parse(f);
    fclose(f);
  }

  ir_dump_typedef();

  ir_cleanup();
  return 0;
}
