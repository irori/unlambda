#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define INITIAL_HEAP_SIZE 512*1024
#define GC_MARGIN 10

typedef enum {
  // Expressions
  I, DOT, K1, K, S2, C2, S1, S, V, D1, D, CONT, C, E, AT, QUES, PIPE, AP,
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
  struct _Cell *l, *r;
} Cell;

static Cell *heap_area, *free_ptr;
static int heap_size, next_heap_size;

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

static void storage_init(int size) {
  heap_size = size;
  heap_area = malloc(sizeof(Cell) * heap_size);
  if (heap_area == NULL)
    errexit("Cannot allocate heap storage (%d cells)\n", heap_size);
    
  free_ptr = heap_area;
  heap_area += heap_size;
  next_heap_size = heap_size * 3 / 2;
}

static inline Cell* new_cell(CellType t, Cell* l, Cell* r) {
  assert(free_ptr < heap_area);
  Cell* c = free_ptr++;
  c->t = t;
  c->l = l;
  c->r = r;
  return c;
}

static inline Cell* new_cell1(CellType t, Cell* l) {
  assert(free_ptr < heap_area);
  Cell* c = free_ptr++;
  c->t = t;
  c->l = l;
  return c;
}

static Cell* copy_cell(Cell* c)
{
  if (!c)
    return NULL;

  if (c->t == COPIED)
    return c->l;

  Cell* r = free_ptr++;
  r->t = c->t;
  r->l = c->l;
  r->r = c->r;
  c->t = COPIED;
  c->l = r;

  switch (r->t) {
    case K1:
    case S1:
    case D1:
    case CONT:
      r->l = copy_cell(r->l);
      break;
    case AP:
    case S2:
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
  static Cell* free_area = NULL;
  int num_alive;
  clock_t start = clock();

  if (free_area == NULL) {
    free_area = malloc(sizeof(Cell) * next_heap_size);
    if (free_area == NULL)
      errexit("Cannot allocate heap storage (%d cells)\n",
	      next_heap_size);
  }

  free_ptr = free_area;
  free_area = heap_area - heap_size;
  heap_area = free_ptr + next_heap_size;

  for (int i = 0; i < nroot; i++) {
    if (roots[i])
      roots[i] = copy_cell(roots[i]);
  }

  num_alive = free_ptr - (heap_area - next_heap_size);
  if (gc_notify)
    fprintf(stderr, "GC: %d / %d\n", num_alive, heap_size);

  if (heap_size != next_heap_size || num_alive * 6 > next_heap_size) {
    heap_size = next_heap_size;
    if (num_alive * 6 > next_heap_size)
      next_heap_size = num_alive * 8;

    free(free_area);
    free_area = NULL;
  }

  total_gc_time += (clock() - start) / (double)CLOCKS_PER_SEC;
}

// Parser -------------------------

static Cell* parse(FILE* fp) {
  enum { preI = 1, preK, preS, preV, preD, preC, preE, preAt, prePipe, ROOT_COUNT };
  Cell* gc_roots[ROOT_COUNT];
  gc_roots[preI] = new_cell(I, NULL, NULL);
  gc_roots[preK] = new_cell(K, NULL, NULL);
  gc_roots[preS] = new_cell(S, NULL, NULL);
  gc_roots[preV] = new_cell(V, NULL, NULL);
  gc_roots[preD] = new_cell(D, NULL, NULL);
  gc_roots[preC] = new_cell(C, NULL, NULL);
  gc_roots[preE] = new_cell(E, NULL, NULL);
  gc_roots[preAt] = new_cell(AT, NULL, NULL);
  gc_roots[prePipe] = new_cell(PIPE, NULL, NULL);

  Cell* stack = NULL;
  Cell* e;
  do {
    if (free_ptr >= heap_area) {
      gc_roots[0] = stack;
      gc_run(gc_roots, ROOT_COUNT);
      stack = gc_roots[0];
    }

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
      stack = new_cell(AP, NULL, stack);
      continue;
    case 'i': case 'I': e = gc_roots[preI]; break;
    case 'k': case 'K': e = gc_roots[preK]; break;
    case 's': case 'S': e = gc_roots[preS]; break;
    case 'v': case 'V': e = gc_roots[preV]; break;
    case 'd': case 'D': e = gc_roots[preD]; break;
    case 'c': case 'C': e = gc_roots[preC]; break;
    case 'e': case 'E': e = gc_roots[preE]; break;
    case 'r': case 'R': e = new_cell1(DOT, (Cell*)'\n'); break;
    case '@': e = gc_roots[preAt]; break;
    case '|': e = gc_roots[prePipe]; break;
    case '.': case '?':
      {
	intptr_t ch2 = fgetc(fp);
	if (ch2 == EOF)
	  errexit("unexpected EOF\n");
	e = new_cell1(ch == '.' ? DOT : QUES, (Cell*)ch2);
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
    if (free_ptr + GC_MARGIN >= heap_area) {
      Cell* roots[3] = {val, task_val, next_cont};
      gc_run(roots, 3);
      val = roots[0];
      task_val = roots[1];
      next_cont = roots[2];
    }

    switch (task) {
    case APP1:
      if (val->t == D) {
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
      if (free_ptr >= heap_area) {
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
    case C2:
      PUSHCONT(DEL, op->r);
      op = op->l;
      goto apply;
    case S1:
      val = (val->t == K1)
	? new_cell(C2, op->l, val->l)
	: new_cell(S2, op->l, val);
      break;
    case S:
      val = new_cell1(S1, val);
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

  storage_init(INITIAL_HEAP_SIZE);

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
