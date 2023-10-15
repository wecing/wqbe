#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "all.h"

typedef struct HashNode HashNode;
struct HashNode {
  char *s;
  HashNode *next;
};

static HashNode *ident_tbl[1024]; /* hash table */

static AgType ag_type_pool[1024]; /* 24 KB */
static int next_ag_id = 0;

static DataDef data_def_pool[1024]; /* 48 KB */
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
  const int entries_cnt = sizeof(ident_tbl) / sizeof(ident_tbl[0]);
  Ident ident = {.slot = 0, .idx = 0};
  HashNode *node = 0, *prev = 0;

  if (s) {
    ident.slot = (hash(s) % (entries_cnt - 1)) + 1;
    node = ident_tbl[ident.slot];
    while (node && strcmp(s, node->s) != 0) {
      ident.idx++;
      prev = node;
      node = node->next;
    }
    if (!node) {
      node = calloc(1, sizeof(*node));
      node->s = strdup(s);
      node->next = 0;
      prev->next = node;
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

static void Ident_cleanup(void) {
  const int entries_cnt = sizeof(ident_tbl) / sizeof(ident_tbl[0]);
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
  for (i = 0; i < next_ag_id; ++i) {
    assert(ag_type_pool[i].body);
    free(ag_type_pool[i].body);
  }
}

static void DataDef_cleanup(void) {
  int i, j, k;
  DataDef *d;
  DataItem *di;
  for (i = 1; i < next_data_def_id; ++i) {
    d = &data_def_pool[i];
    assert(d->items);
    for (j = 0; j < d->items_len; ++j) {
      assert(d->items[j].items);
      for (k = 0; k < d->items[j].items_len; ++k) {
        di = &d->items[j].items[k];
        if (di->t == DI_STR) {
          assert(di->u.str);
          free(di->u.str);
        }
      }
      free(d->items[j].items);
    }
    free(d->items);

    if(d->linkage.sec_name)
      free(d->linkage.sec_name);
    if(d->linkage.sec_flags)
      free(d->linkage.sec_flags);
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
  /* TODO: remove */
  (void)blk_pool;
  (void)next_blk_id;

  Ident_cleanup();
  AgType_cleanup();
  DataDef_cleanup();
  Instr_cleanup();
  FuncDef_cleanup();
}
