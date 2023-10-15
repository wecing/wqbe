#include <assert.h>

#include "all.h"

int main(void) {
  assert(sizeof(Type) == 4);
  assert(sizeof(ArrType) == 8);
  assert(sizeof(AgType) == 24);
  assert(sizeof(DataDef) == 48);
  assert(sizeof(Block) == 12);
  assert(sizeof(FuncDef) == 56);
  assert(sizeof(Instr) == 72);

  ir_cleanup();
  return 0;
}
