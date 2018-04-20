#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define INITIAL_HEAP_SIZE 512*1024
#define GC_MARGIN 10

typedef enum {
  // Expressions
  I, DOT, K1, K, S2, S1, S, V, D1, D, CONT, C, E, AT, QUES, PIPE, AP,
  // Continuations
  APP1,
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

static Cell constI = {I};
static Cell constK = {K};
static Cell constS = {S};
static Cell constV = {V};
static Cell constD = {D};
static Cell constC = {C};
static Cell constE = {E};
static Cell constAt = {AT};
static Cell constPipe = {PIPE};

static Cell *heap_area, *free_ptr;
static int heap_size, next_heap_size;

static int gc_notify = 0;
static double total_gc_time = 0.0;

void errexit(char *fmt, ...) {
    va_list arg;
    va_start(arg, fmt);
    vfprintf(stderr, fmt, arg);
    va_end(arg);

    exit(1);
}

// Storage -------------------------

void storage_init(int size) {
    heap_size = size;
    heap_area = malloc(sizeof(Cell) * heap_size);
    if (heap_area == NULL)
	errexit("Cannot allocate heap storage (%d cells)\n", heap_size);
    
    free_ptr = heap_area;
    heap_area += heap_size;
    next_heap_size = heap_size * 3 / 2;  
}

inline Cell* new_cell(CellType t, Cell* l, Cell* r) {
  assert(free_ptr < heap_area);
  Cell* c = free_ptr++;
  c->t = t;
  c->l = l;
  c->r = r;
  return c;
}

Cell* copy_cell(Cell* c)
{
  if (!c)
    return NULL;

  switch (c->t) {
  case COPIED:
    return c->l;
  case I: case K: case S: case V: case D: case C: case E: case AT: case PIPE:
    return c;
  default:
    break;
  }

  Cell* r = free_ptr++;
  r->t = c->t;
  r->l = c->l;
  r->r = c->r;
  c->t = COPIED;
  c->l = r;
  return r;
}

void gc_run(Cell** roots, int nroot) {
  static Cell* free_area = NULL;
  int num_alive;
  Cell* scan;
  clock_t start = clock();

  if (free_area == NULL) {
    free_area = malloc(sizeof(Cell) * next_heap_size);
    if (free_area == NULL)
      errexit("Cannot allocate heap storage (%d cells)\n",
	      next_heap_size);
  }

  free_ptr = scan = free_area;
  free_area = heap_area - heap_size;
  heap_area = free_ptr + next_heap_size;

  for (int i = 0; i < nroot; i++) {
    if (roots[i])
      roots[i] = copy_cell(roots[i]);
  }

  while (scan < free_ptr) {
    switch (scan->t) {
    case COPIED:
      errexit("[BUG] cannot happen\n");
      break;
    case K1:
    case S1:
    case D1:
    case CONT:
      scan->l = copy_cell(scan->l);
      break;
    case AP:
    case S2:
    case APP1:
    case APP:
    case DEL:
      scan->l = copy_cell(scan->l);
      scan->r = copy_cell(scan->r);
      break;
    default:
      break;
    }
    scan++;
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

Cell* parse(FILE* fp) {
  Cell* stack = NULL;
  Cell* e;
  do {
    if (free_ptr >= heap_area)
      gc_run(&stack, 1);

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
    case 'i': case 'I': e = &constI; break;
    case 'k': case 'K': e = &constK; break;
    case 's': case 'S': e = &constS; break;
    case 'v': case 'V': e = &constV; break;
    case 'd': case 'D': e = &constD; break;
    case 'c': case 'C': e = &constC; break;
    case 'e': case 'E': e = &constE; break;
    case 'r': case 'R': e = new_cell(DOT, (Cell*)'\n', NULL); break;
    case '@': e = &constAt; break;
    case '|': e = &constPipe; break;
    case '.': case '?':
      {
	intptr_t ch2 = fgetc(fp);
	if (ch2 == EOF)
	  errexit("unexpected EOF\n");
	e = new_cell(ch == '.' ? DOT : QUES, (Cell*)ch2, NULL);
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

Cell* load_program(const char* fname) {
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

void run(Cell* val) {
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
	val = new_cell(D1, task_val, NULL);
	POPCONT;
	break;
      } else {
	Cell* rand = task_val;
	task = APP;
	task_val = val;
	val = rand;
	goto eval;
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
      val = new_cell(K1, val, NULL);
      break;
    case S2:
      {
	Cell* e2 = new_cell(AP, op->r, val);
	PUSHCONT(APP1, e2);
	PUSHCONT(APP1, val);
	val = op->l;
	break;
      }
    case S1:
      val = new_cell(S2, op->l, val);
      break;
    case S:
      val = new_cell(S1, val, NULL);
      break;
    case V:
      val = op;
      break;
    case D1:
      PUSHCONT(DEL, val);
      val = op->l;
      goto eval;
    case D:
      val = new_cell(D1, val, NULL);
      break;
    case CONT:
      next_cont = op->l;
      POPCONT;
      break;
    case C:
      PUSHCONT(APP, val);
      val = new_cell(CONT, next_cont, NULL);
      break;
    case E:
      task = FINAL;
      break;
    case AT:
      current_ch = getchar();
      PUSHCONT(APP, val);
      val = current_ch == EOF ? &constV : &constI;
      break;
    case QUES:
      PUSHCONT(APP, val);
      val = current_ch == (int)op->l ? &constI : &constV;
      break;
    case PIPE:
      PUSHCONT(APP, val);
      val = current_ch == EOF ? &constV : new_cell(DOT, (Cell*)current_ch, NULL);
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
