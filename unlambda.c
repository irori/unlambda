#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef enum {
  // Expressions
  I, DOT, K1, K, S2, B2, C2, S1, B1, S, V, D1, D, CONT, C, E, AT, QUES, PIPE, AP,
  // Continuations
  APP1,
  APPS,
  APP,
  DEL,
  FINAL,
  // GC
  COPIED,
} CellType;

typedef struct _Cell {
  CellType t;
  uint8_t age;
  uint8_t mark;
  struct _Cell *l, *r;
} Cell;

static int gc_notify = 0;
static double total_gc_time = 0.0;

static void errexit(char *fmt, ...) {
  va_list arg;
  va_start(arg, fmt);
  vfprintf(stderr, fmt, arg);
  va_end(arg);

  exit(1);
}

// Storage -------------------------

#define YOUNG_SIZE (256*1024)
#define HEAP_CHUNK_SIZE (256*1024-1)
#define AGE_MAX 2

Cell young1[YOUNG_SIZE];
Cell young2[YOUNG_SIZE];

typedef struct _HeapChunk {
  Cell cells[HEAP_CHUNK_SIZE];
  struct _HeapChunk *next;
} HeapChunk;

HeapChunk* old_area;
Cell* free_list;

Cell *free_ptr, *young_area_end, *next_young_area;
Cell** gc_roots;
int gc_nroot;

static void grow_heap() {
  HeapChunk* chunk = malloc(sizeof(HeapChunk));
  if (chunk == NULL)
    errexit("Cannot allocate heap chunk\n");
  chunk->next = old_area;
  old_area = chunk;

  for (int i = 0; i < HEAP_CHUNK_SIZE - 1; i++)
    chunk->cells[i].l = &chunk->cells[i + 1];
  chunk->cells[HEAP_CHUNK_SIZE - 1].l = free_list;
  free_list = chunk->cells;
}

static void storage_init() {
  free_ptr = young1;
  young_area_end = free_ptr + YOUNG_SIZE;
  next_young_area = young2;

  grow_heap();
}

static inline Cell* new_cell(CellType t, Cell* l, Cell* r) {
  assert(free_ptr < young_area_end);
  Cell* c = free_ptr++;
  c->t = t;
  c->age = 0;
  c->l = l;
  c->r = r;
  return c;
}

static inline Cell* new_cell1(CellType t, Cell* l) {
  assert(free_ptr < young_area_end);
  Cell* c = free_ptr++;
  c->t = t;
  c->age = 0;
  c->l = l;
  return c;
}

static void mark(Cell* c) {
  if (!c || c->mark)
    return;

  if (c->t == COPIED)
    c = c->l;
  c->mark = 1;

  switch (c->t) {
  case K1:
  case S1:
  case B1:
  case D1:
  case CONT:
    mark(c->l);
    break;
  case AP:
  case S2:
  case B2:
  case C2:
  case APP1:
  case APPS:
  case APP:
  case DEL:
    mark(c->l);
    mark(c->r);
    break;
  default:
    break;
  }
}

static void major_gc() {
  for (int i = 0; i < gc_nroot; i++) {
    if (gc_roots[i])
      mark(gc_roots[i]);
  }
  int freed = 0, total = 0;
  for (HeapChunk* chunk = old_area; chunk; chunk = chunk->next) {
    for (int i = 0; i < HEAP_CHUNK_SIZE; i++) {
      if (chunk->cells[i].mark)
	chunk->cells[i].mark = 0;
      else {
	chunk->cells[i].l = free_list;
	free_list = &chunk->cells[i];
	freed++;
      }
    }
    total += HEAP_CHUNK_SIZE;
  }
  if (gc_notify)
    fprintf(stderr, "%d / %d cells freed\n", freed, total);

  for (int i = 0; i < YOUNG_SIZE; i++)
    young1[i].mark = 0;
  for (int i = 0; i < YOUNG_SIZE; i++)
    young2[i].mark = 0;

  if (freed < HEAP_CHUNK_SIZE)
    grow_heap();
}

static Cell* copy_cell(Cell* c)
{
  if (!c)
    return NULL;

  if (c->t == COPIED)
    return c->l;

  if (c->age > AGE_MAX)
    return c;  // Already promoted

  Cell* r;
  if (c->age == AGE_MAX) {
    if (!free_list)
      major_gc();
    // Promotion
    r = free_list;
    free_list = free_list->l;
  } else {
    r = free_ptr++;
  }
  *r = *c;
  r->age++;
  c->t = COPIED;
  c->l = r;

  switch (r->t) {
  case K1:
  case S1:
  case B1:
  case D1:
  case CONT:
    r->l = copy_cell(r->l);
    break;
  case AP:
  case S2:
  case B2:
  case C2:
  case APP1:
  case APPS:
  case APP:
  case DEL:
    r->l = copy_cell(r->l);
    r->r = copy_cell(r->r);
    break;
  default:
    break;
  }

  return r;
}

static void gc_run(Cell** roots, int nroot) {
  int num_alive;
  clock_t start = clock();

  gc_roots = roots;
  gc_nroot = nroot;

  free_ptr = next_young_area;
  next_young_area = young_area_end - YOUNG_SIZE;
  young_area_end = free_ptr + YOUNG_SIZE;

  for (int i = 0; i < nroot; i++) {
    if (roots[i])
      roots[i] = copy_cell(roots[i]);
  }

  num_alive = free_ptr - (young_area_end - YOUNG_SIZE);
  if (gc_notify)
    fprintf(stderr, "Minor GC: %d\n", num_alive);

  total_gc_time += (clock() - start) / (double)CLOCKS_PER_SEC;
}

// Parser -------------------------

static Cell* allocate_from_old(CellType t, Cell* l, Cell* r) {
  if (!free_list)
    grow_heap();

  Cell* c = free_list;
  free_list = free_list->l;
  c->t = t;
  c->age = AGE_MAX + 1;
  c->mark = 0;
  c->l = l;
  c->r = r;
  return c;
}

static Cell* parse(FILE* fp) {
  Cell *preI = allocate_from_old(I, NULL, NULL);
  Cell *preK = allocate_from_old(K, NULL, NULL);
  Cell *preS = allocate_from_old(S, NULL, NULL);
  Cell *preV = allocate_from_old(V, NULL, NULL);
  Cell *preD = allocate_from_old(D, NULL, NULL);
  Cell *preC = allocate_from_old(C, NULL, NULL);
  Cell *preE = allocate_from_old(E, NULL, NULL);
  Cell *preAt = allocate_from_old(AT, NULL, NULL);
  Cell *prePipe = allocate_from_old(PIPE, NULL, NULL);

  Cell* stack = NULL;
  Cell* e;
  do {
    int ch;
    do {
      ch = fgetc(fp);
      if (ch == '#') {
	while (ch = fgetc(fp), ch != '\n' && ch != EOF)
	  ;
      }
    } while (isspace(ch));
    switch (ch) {
    case '`':
      stack = allocate_from_old(AP, NULL, stack);
      continue;
    case 'i': case 'I': e = preI; break;
    case 'k': case 'K': e = preK; break;
    case 's': case 'S': e = preS; break;
    case 'v': case 'V': e = preV; break;
    case 'd': case 'D': e = preD; break;
    case 'c': case 'C': e = preC; break;
    case 'e': case 'E': e = preE; break;
    case 'r': case 'R': e = allocate_from_old(DOT, (Cell*)'\n', NULL); break;
    case '@': e = preAt; break;
    case '|': e = prePipe; break;
    case '.': case '?':
      {
	intptr_t ch2 = fgetc(fp);
	if (ch2 == EOF)
	  errexit("unexpected EOF\n");
	e = allocate_from_old(ch == '.' ? DOT : QUES, (Cell*)ch2, NULL);
	break;
      }
    case EOF:
      errexit("unexpected EOF\n");
      break;
    default:
      errexit("unexpected character %c\n", ch);
      break;
    }
    while (stack) {
      if (!stack->l) {
	stack->l = e;
	break;
      }
      Cell* next = stack->r;
      stack->r = e;
      e = stack;
      stack = next;
    }
  } while (stack);
  return e;
}

static Cell* load_program(const char* fname) {
  FILE* fp;
  Cell* c;

  if (fname == NULL)
    fp = stdin;
  else {
    fp = fopen(fname, "r");
    if (fp == NULL)
      errexit("cannot open %s\n", fname);
  }

  c = parse(fp);

  if (fname != NULL)
    fclose(fp);

  return c;
}

// Evaluator
#define PUSHCONT(t, v) (next_cont = new_cell(task, next_cont, task_val), task = t, task_val = v)
#define POPCONT (task = next_cont->t, task_val = next_cont->r, next_cont = next_cont->l)

static void run(Cell* val) {
  intptr_t current_ch = EOF;
  Cell* next_cont = NULL;
  Cell* op;

  CellType task = FINAL;
  Cell* task_val = NULL;

  goto eval;

  for (;;) {
    switch (task) {
    case APP1:
      if (val->t == D) {
	if (free_ptr >= young_area_end) {
	  Cell* roots[3] = {val, task_val, next_cont};
	  gc_run(roots, 3);
	  val = roots[0];
	  task_val = roots[1];
	  next_cont = roots[2];
	}
	val = new_cell1(D1, task_val);
	POPCONT;
	break;
      } else {
	Cell* rand = task_val;
	task = APP;
	task_val = val;
	val = rand;
	goto eval;
      }
    case APPS:
      if (val->t == D) {
	if (free_ptr >= young_area_end) {
	  Cell* roots[3] = {val, task_val, next_cont};
	  gc_run(roots, 3);
	  val = roots[0];
	  task_val = roots[1];
	  next_cont = roots[2];
	}
	val = new_cell1(D1, task_val);
	POPCONT;
	break;
      } else {
	Cell* rand = task_val;
	task = APP;
	task_val = val;
	op = rand->l;
	val = rand->r;
	goto apply;
      }
    case APP:
      op = task_val;
      POPCONT;
      goto apply;
    case DEL:
      op = val;
      val = task_val;
      POPCONT;
      goto apply;
    case FINAL:
      return;
    default:
      errexit("[BUG] run: invalid task type %d\n", task);
    }
    continue;
  eval:
    while (val->t == AP) {
      if (free_ptr >= young_area_end) {
	Cell* roots[3] = {val, task_val, next_cont};
	gc_run(roots, 3);
	val = roots[0];
	task_val = roots[1];
	next_cont = roots[2];
      }
      PUSHCONT(APP1, val->r);
      val = val->l;
    }
    continue;
  apply:
    if (free_ptr + 1 >= young_area_end) {
      Cell* roots[4] = {val, task_val, next_cont, op};
      gc_run(roots, 4);
      val = roots[0];
      task_val = roots[1];
      next_cont = roots[2];
      op = roots[3];
    }
    switch (op->t) {
    case I:
      break;
    case DOT:
      putchar((int)op->l);
      break;
    case K1:
      val = op->l;
      break;
    case K:
      val = new_cell1(K1, val);
      break;
    case S2:
      {
	Cell* e2 = new_cell(AP, op->r, val);
	PUSHCONT(APPS, e2);
	op = op->l;
	goto apply;
      }
    case B2:
      if (op->l->t == D) {
	Cell* e2 = new_cell(AP, op->r, val);
	val = new_cell1(D1, e2);
	break;
      } else {
	PUSHCONT(APP, op->l);
	op = op->r;
	goto apply;
      }
    case C2:
      PUSHCONT(DEL, op->r);
      op = op->l;
      goto apply;
    case S1:
      val = (val->t == K1)
	? new_cell(C2, op->l, val->l)
	: new_cell(S2, op->l, val);
      break;
    case B1:
      val = new_cell(B2, op->l, val);
      break;
    case S:
      val = (val->t == K1)
	? new_cell1(B1, val->l)
	: new_cell1(S1, val);
      break;
    case V:
      val = op;
      break;
    case D1:
      PUSHCONT(DEL, val);
      val = op->l;
      goto eval;
    case D:
      val = new_cell1(D1, val);
      break;
    case CONT:
      next_cont = op->l;
      POPCONT;
      break;
    case C:
      PUSHCONT(APP, val);
      val = new_cell1(CONT, next_cont);
      break;
    case E:
      task = FINAL;
      break;
    case AT:
      current_ch = getchar();
      PUSHCONT(APP, val);
      val = new_cell(current_ch == EOF ? V : I, NULL, NULL);
      break;
    case QUES:
      PUSHCONT(APP, val);
      val = new_cell(current_ch == (int)op->l ? I : V, NULL, NULL);
      break;
    case PIPE:
      PUSHCONT(APP, val);
      val = new_cell1(current_ch == EOF ? V : DOT, (Cell*)current_ch);
      break;
    default:
      errexit("[BUG] apply: invalid operator type %d\n", op->t);
    }
  }
}

int main(int argc, char *argv[]) {
  Cell* root;
  clock_t start;
  char *prog_file = NULL;
  int i;
  int print_stats = 0;
    
  for (i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-g") == 0)
      gc_notify = 1;
    else if (strcmp(argv[i], "-s") == 0)
      print_stats = 1;
    else if (strcmp(argv[i], "-u") == 0)
      setbuf(stdout, NULL);
    else
      prog_file = argv[i];
  }

  storage_init();

  root = load_program(prog_file);

  start = clock();
  run(root);

  if (print_stats) {
    double evaltime = (clock() - start) / (double)CLOCKS_PER_SEC;

    printf("  total eval time --- %5.2f sec.\n", evaltime - total_gc_time);
    printf("  total gc time   --- %5.2f sec.\n", total_gc_time);
  }
  return 0;
}
