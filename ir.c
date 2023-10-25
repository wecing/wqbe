#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"

typedef struct HashNode HashNode;
struct HashNode {
  char *s;
  HashNode *next;
};

static HashNode *ident_tbl[1024]; /* 16 KB; hash table */

static AgType ag_type_pool[1024]; /* 16 KB */
static int next_ag_id = 1;

static DataDef data_def_pool[1024]; /* 40 KB */
static int next_data_def_id = 1;

static Instr instr_pool[1024]; /* 72 KB */
static int next_instr_id = 1;

static Block blk_pool[1024]; /* 12 KB */
static int next_blk_id = 1;

static FuncDef func_def_pool[1024]; /* 56 KB */
static int next_func_def_id = 1;

/* djb2 hashing */
static unsigned long hash(const char *s) {
  char c;
  unsigned long hash = 5381;
  while ((c = *s++) != 0) {
    hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
  }
  return hash;
}

Ident Ident_from_str(const char *s) {
  const int entries_cnt = countof(ident_tbl);
  Ident ident = {.slot = 0, .idx = 0};
  HashNode *node = 0, **node_p = 0;

  if (s) {
    ident.slot = (hash(s) % (entries_cnt - 1)) + 1;
    node_p = &ident_tbl[ident.slot];
    node = *node_p;
    while (node && node->s && strcmp(s, node->s) != 0) {
      ident.idx++;
      node_p = &node->next;
      node = *node_p;
    }
    if (!node) {
      node = calloc(1, sizeof(*node));
      node->s = strdup(s);
      node->next = 0;
      *node_p = node;
    }
  }
  return ident;
}

/* returns null if input is 0 */
const char *Ident_to_str(Ident s) {
  HashNode *node;
  uint16_t rem_steps;

  node = ident_tbl[s.slot];
  rem_steps = s.idx;
  assert(node);
  while (rem_steps--) {
    node = node->next;
    assert(node);
  }
  return node->s;
}

int Ident_eq(Ident x, Ident y) { return x.slot == y.slot && x.idx == y.idx; }

int Type_is_subty(Type t) {
  switch (t.t) {
  case TP_W: case TP_L: case TP_S: case TP_D:
  case TP_B: case TP_H:
  case TP_AG:
    return 1;
  }
  return 0;
}

int Type_is_extty(Type t) {
  switch (t.t) {
  case TP_W: case TP_L: case TP_S: case TP_D:
  case TP_B: case TP_H:
    return 1;
  }
  return 0;
}

Type AgType_lookup_or_fail(Ident ident) {
  int prev = next_ag_id;
  Type t = AgType_lookup_or_alloc(ident);
  check(t.ag_id != prev, "type %s not found", Ident_to_str(ident));
  return t;
}

Type AgType_lookup_or_alloc(Ident ident) {
  int i;
  Type t = {0};
  t.t = TP_AG;
  for (i = 1; i < next_ag_id; ++i) {
    if (Ident_eq(ag_type_pool[i].ident, ident)) {
      t.ag_id = i;
      return t;
    }
  }

  assert((uint64_t) next_ag_id < countof(ag_type_pool) - 1);
  ag_type_pool[next_ag_id].ident = ident;
  t.ag_id = next_ag_id++;
  return t;
}

AgType *AgType_get(Type t) {
  assert(t.t == TP_AG);
  assert(t.ag_id != 0);
  return &ag_type_pool[t.ag_id];
}

uint16_t DataDef_alloc(Ident ident) {
  int r = next_data_def_id++;
  check(DataDef_lookup(ident) == 0 && FuncDef_lookup(ident) == 0,
        "redefinition of '%s'", Ident_to_str(ident));
  assert((uint64_t) next_data_def_id < countof(data_def_pool));
  data_def_pool[r].ident = ident;
  return r;
}

uint16_t DataDef_lookup(Ident ident) {
  int i;
  for (i = 1; i < next_data_def_id; ++i) {
    if (Ident_eq(ident, data_def_pool[i].ident)) {
      return i;
    }
  }
  return 0;
}

DataDef *DataDef_get(uint16_t id) {
  if (id == 0) return 0;
  assert((int) id < next_data_def_id);
  return &data_def_pool[id];
}

uint16_t FuncDef_alloc(Ident ident) {
  int r = next_func_def_id++;
  check(DataDef_lookup(ident) == 0 && FuncDef_lookup(ident) == 0,
        "redefinition of '%s'", Ident_to_str(ident));
  assert((uint64_t) next_func_def_id < countof(func_def_pool));
  func_def_pool[r].ident = ident;
  return r;
}

uint16_t FuncDef_lookup(Ident ident) {
  int i;
  for (i = 1; i < next_func_def_id; ++i) {
    if (Ident_eq(ident, func_def_pool[i].ident)) {
      return i;
    }
  }
  return 0;
}

FuncDef *FuncDef_get(uint16_t id) {
  if (id == 0) return 0;
  assert((int) id < next_func_def_id);
  return &func_def_pool[id];
}

static void dump_type(Type t) {
  switch (t.t) {
  case TP_W: printf("w"); break;
  case TP_L: printf("l"); break;
  case TP_S: printf("s"); break;
  case TP_D: printf("d"); break;
  case TP_B: printf("b"); break;
  case TP_H: printf("h"); break;
  case TP_SB: printf("sb"); break;
  case TP_SH: printf("sh"); break;
  case TP_UB: printf("ub"); break;
  case TP_UH: printf("uh"); break;
  case TP_AG:
    printf("%s", Ident_to_str(AgType_get(t)->ident));
    break;
  case TP_NONE:
    break;
  default:
    fail("unrecognized TYPE kind: %d", t.t);
  }
}

static void dump_sb(ArrType *sb) {
  printf("{");
  while (sb->t.t != TP_UNKNOWN) {
    printf(" ");
    dump_type(sb->t);
    printf(" %d%c", sb->count, sb[1].t.t == TP_UNKNOWN ? ' ' : ',');
    sb++;
  }
  printf("}");
}

void ir_dump_typedef(void) {
  int i;
  AgType ag;
  ArrType **ub;
  for (i = 1; i < next_ag_id; ++i) {
    ag = ag_type_pool[i];
    printf("type %s = align %d ", Ident_to_str(ag.ident), 1 << ag.log_align);
    if (ag.is_opaque) {
      printf("{ %d }", ag.size);
    } else if (ag.is_union) {
      ub = ag.u.ub;
      printf("{");
      while (*ub) {
        printf(" ");
        dump_sb(*ub++);
      }
      printf(" }");
    } else {
      dump_sb(ag.u.sb);
    }
    printf("\n");
  }
}

void ir_dump_datadef(uint16_t id) {
  DataDef *dd;

  while (id) {
    dd = DataDef_get(id);
    /* TODO: dump DATADEF */

    id = dd->next_id;
  }
}

static void Ident_cleanup(void) {
  const int entries_cnt = countof(ident_tbl);
  HashNode *node, *t;
  int i;

  for (i = 1; i < entries_cnt; ++i) {
    node = ident_tbl[i];
    while (node) {
      t = node;
      node = node->next;
      free(t->s);
      free(t);
    }
  }
}

static void AgType_cleanup(void) {
  int i;
  ArrType **ub;
  for (i = 1; i < next_ag_id; ++i) {
    if (ag_type_pool[i].is_opaque) {
      continue;
    } else if (ag_type_pool[i].is_union) {
      ub = ag_type_pool[i].u.ub;
      while (*ub) {
        free(*ub++);
      }
      free(ag_type_pool[i].u.ub);
    } else {
      free(ag_type_pool[i].u.sb);
    }
  }
}

static void DataDef_cleanup(void) {
  int i, j, k;
  DataDef *dd;
  DataItem *p;
  for (i = 1; i < next_data_def_id; ++i) {
    dd = &data_def_pool[i];
    assert(dd->items);
    for (j = 0; !dd->items[j].is_dummy_item; ++j) {
      if (!dd->items[j].is_ext_ty) continue;
      p = dd->items[j].u.ext_ty.items;
      assert(p);
      for (k = 0; p[k].t != DI_UNKNOWN; ++k) {
        if (p[k].t != DI_STR) continue;
        assert(p[k].u.str);
        free(p[k].u.str);
      }
      free(p);
    }
    free(dd->items);

    if(dd->linkage.sec_name)
      free(dd->linkage.sec_name);
    if(dd->linkage.sec_flags)
      free(dd->linkage.sec_flags);
  }
}

static void Instr_cleanup(void) {
  int i;
  for (i = 1; i < next_instr_id; ++i) {
    if (instr_pool[i].t == I_CALL) {
      if (instr_pool[i].u.call.args)
        free(instr_pool[i].u.call.args);
    } else if (instr_pool[i].t == I_PHI) {
      if (instr_pool[i].u.phi.args)
        free(instr_pool[i].u.phi.args);
    }
  }
}

static void FuncDef_cleanup(void) {
  int i;
  FuncDef *p;
  for (i = 1; i < next_func_def_id; ++i) {
    p = &func_def_pool[i];
    if(p->linkage.sec_name)
      free(p->linkage.sec_name);
    if(p->linkage.sec_flags)
      free(p->linkage.sec_flags);
    if (p->params)
      free(p->params);
  }
}

void ir_cleanup(void) {
  /* TODO: parse blocks and remove */
  (void)blk_pool;
  (void)next_blk_id;

  FuncDef_cleanup();
  Instr_cleanup();
  DataDef_cleanup();
  AgType_cleanup();
  Ident_cleanup();
}
