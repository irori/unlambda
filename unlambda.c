// Unlambda interpreter
//
// Copyright (c) 2018 Kunihiko Sakamoto <irorin@gmail.com>
// This code is licensed under the MIT License (see LICENSE file for details).

#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define VERSION "1.0.0"

// Verbosity levels
enum {
  V_NONE,
  V_STATS,
  V_MAJOR_GC,
  V_MINOR_GC,
} verbosity = V_NONE;

static void errexit(char *fmt, ...) {
  va_list arg;
  va_start(arg, fmt);
  vfprintf(stderr, fmt, arg);
  va_end(arg);
  exit(1);
}

// Storage management --------------------------------------------------

typedef enum {
  // Expressions
  I, DOT, K1, K, S2, B2, C2, V2, S1, B1, T1, S, V, D1, D, CONT, C, E, AT, QUES, PIPE, AP,
  // Continuations
  EVAL_RIGHT, EVAL_RIGHT_S, APPLY, APPLY_T, EXIT,
  // GC
  COPIED,
} CellType;

typedef struct _Cell {
  CellType t;
  uint8_t ch;  // for DOT and QUES
  uint8_t age;
  bool marked;
  struct _Cell *l, *r;
} Cell;

#define YOUNG_SIZE (256*1024)
#define HEAP_CHUNK_SIZE (256*1024-1)
#define AGE_MAX 2
#define INITIAL_MARK_STACK_SIZE (64*1024)

Cell young1[YOUNG_SIZE];
Cell young2[YOUNG_SIZE];

typedef struct _HeapChunk {
  Cell cells[HEAP_CHUNK_SIZE];
  struct _HeapChunk *next;
} HeapChunk;

HeapChunk* old_area;
Cell* free_list;

Cell *free_ptr, *young_area_end, *next_young_area;

static double total_gc_time = 0.0;
static int major_gc_count = 0;
static int minor_gc_count = 0;

static void grow() {
  HeapChunk* chunk = malloc(sizeof(HeapChunk));
  if (chunk == NULL)
    errexit("Out of memory\n");
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
  grow();
}

static inline Cell* new_cell(CellType t, Cell* l, Cell* r) {
  Cell* c = free_ptr++;
  c->t = t;
  c->age = 0;
  c->l = l;
  c->r = r;
  return c;
}

static inline Cell* new_cell1(CellType t, Cell* l) {
  Cell* c = free_ptr++;
  c->t = t;
  c->age = 0;
  c->l = l;
  return c;
}

static inline Cell* new_cell0(CellType t) {
  Cell* c = free_ptr++;
  c->t = t;
  c->age = 0;
  return c;
}

static void mark(Cell* roots[], int nroot) {
  int stack_size = INITIAL_MARK_STACK_SIZE;
  Cell** stack = malloc(sizeof(Cell*) * stack_size);
  if (!stack)
    errexit("Out of memory\n");
  int i;
  for (i = 0; i < nroot; i++)
    stack[i] = roots[i];

  while (i) {
    Cell* c = stack[--i];
  top:
    if (!c || c->marked)
      continue;
    if (c->t == COPIED)
      c = c->l;
    c->marked = true;

    switch (c->t) {
    case K1:
    case S1:
    case B1:
    case D1:
    case T1:
    case CONT:
      c = c->l;
      goto top;
    case AP:
    case S2:
    case B2:
    case C2:
    case V2:
    case EVAL_RIGHT:
    case EVAL_RIGHT_S:
    case APPLY:
    case APPLY_T:
      if (i >= stack_size) {
        stack_size *= 2;
        stack = realloc(stack, sizeof(Cell*) * stack_size);
        if (!stack)
          errexit("Out of memory\n");
      }
      stack[i++] = c->r;
      c = c->l;
      goto top;
    default:
      break;
    }
  }
  free(stack);
}

static void major_gc(Cell* roots[], int nroot) {
  mark(roots, nroot);

  // Sweep
  int freed = 0, total = 0;
  for (HeapChunk* chunk = old_area; chunk; chunk = chunk->next) {
    for (int i = 0; i < HEAP_CHUNK_SIZE; i++) {
      if (chunk->cells[i].marked)
        chunk->cells[i].marked = false;
      else {
        chunk->cells[i].l = free_list;
        free_list = &chunk->cells[i];
        freed++;
      }
    }
    total += HEAP_CHUNK_SIZE;
  }
  if (verbosity >= V_MAJOR_GC)
    fprintf(stderr, "%d / %d cells freed\n", freed, total);

  for (int i = 0; i < YOUNG_SIZE; i++)
    young1[i].marked = false;
  for (int i = 0; i < YOUNG_SIZE; i++)
    young2[i].marked = false;

  while (freed < total / 5) {
    grow();
    freed += HEAP_CHUNK_SIZE;
    total += HEAP_CHUNK_SIZE;
  }
  major_gc_count++;
}

static Cell* copy_cell(Cell* c) {
  if (!c)
    return NULL;

  if (c->t == COPIED)
    return c->l;

  if (c->age > AGE_MAX)
    return c;  // Already promoted

  Cell* r;
  if (c->age == AGE_MAX) {
    // Promotion
    r = free_list;
    free_list = free_list->l;
    free_ptr->t = COPIED;
    free_ptr->l = r;
    free_ptr++;
  } else {
    r = free_ptr++;
  }
  *r = *c;
  r->age++;
  c->t = COPIED;
  c->l = r;
  return r;
}

static void gc_run(Cell* roots[], int nroot) {
  clock_t start = clock();

  Cell* scan = free_ptr = next_young_area;
  next_young_area = young_area_end - YOUNG_SIZE;
  young_area_end = free_ptr + YOUNG_SIZE;

  for (int i = 0; i < nroot; i++) {
    if (!free_list)
      major_gc(roots, nroot);
    if (roots[i])
      roots[i] = copy_cell(roots[i]);
  }

  while (scan < free_ptr) {
    if (!free_list)
      major_gc(roots, nroot);
    Cell* c = scan;
    if (c->t == COPIED)
      c = c->l;
    switch (c->t) {
    case COPIED:
      errexit("[BUG] cannot happen\n");
      break;
    case K1:
    case S1:
    case B1:
    case D1:
    case T1:
    case CONT:
      c->l = copy_cell(c->l);
      break;
    case AP:
    case S2:
    case B2:
    case C2:
    case V2:
    case EVAL_RIGHT:
    case EVAL_RIGHT_S:
    case APPLY:
    case APPLY_T:
      c->l = copy_cell(c->l);
      if (!free_list)
        major_gc(roots, nroot);
      c->r = copy_cell(c->r);
      break;
    default:
      break;
    }
    scan++;
  }

  if (verbosity >= V_MINOR_GC) {
    long num_alive = free_ptr - (young_area_end - YOUNG_SIZE);
    fprintf(stderr, "Minor GC: %ld\n", num_alive);
  }

  minor_gc_count++;
  total_gc_time += (clock() - start) / (double)CLOCKS_PER_SEC;
}

// Parser --------------------------------------------------------------

static Cell* allocate_from_old(CellType t, Cell* l, Cell* r) {
  if (!free_list)
    grow();

  Cell* c = free_list;
  free_list = free_list->l;
  c->t = t;
  c->age = AGE_MAX + 1;
  c->marked = false;
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
    case 'r': case 'R': e = allocate_from_old(DOT, NULL, NULL); e->ch = '\n'; break;
    case '@': e = preAt; break;
    case '|': e = prePipe; break;
    case '.': case '?':
      {
        int ch2 = fgetc(fp);
        if (ch2 == EOF)
          errexit("unexpected EOF\n");
        e = allocate_from_old(ch == '.' ? DOT : QUES, NULL, NULL);
        e->ch = ch2;
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
  if (fname == NULL)
    fp = stdin;
  else {
    fp = fopen(fname, "r");
    if (fp == NULL)
      errexit("cannot open %s\n", fname);
  }

  Cell* c = parse(fp);

  if (fname == NULL) {
    // If both program and input are from stdin, discard the rest of the
    // current line, for convenience
    int ch;
    do {
      ch = getchar();
    } while (ch != EOF && ch != '\n');
  } else {
    fclose(fp);
  }
  return c;
}

// Evaluator -----------------------------------------------------------

#define PUSHCONT(t, v) (next_cont = new_cell(task, next_cont, task_val), task = t, task_val = v)
#define POPCONT (task = next_cont->t, task_val = next_cont->r, next_cont = next_cont->l)

void run(Cell* val) {
  int current_ch = EOF;
  Cell* next_cont = NULL;
  Cell* op;

  CellType task = EXIT;
  Cell* task_val = NULL;

  goto eval;

  for (;;) {
    switch (task) {
    case EVAL_RIGHT:
      // Evaluate `<val><task_val>.
      if (val->t == D) {
        op = val;
        val = task_val;
        POPCONT;
        goto apply;
      } else {
        Cell* rand = task_val;
        task = APPLY;
        task_val = val;
        val = rand;
        goto eval;
      }
    case EVAL_RIGHT_S:
      // Evaluate `<val><task_val>, task_val is of the form `<v1><v2>
      // where v1 and v2 are already evaluated.
      if (val->t == D) {
        op = val;
        val = task_val;
        POPCONT;
      } else {
        Cell* rand = task_val;
        task = APPLY;
        task_val = val;
        op = rand->l;
        val = rand->r;
      }
      goto apply;
    case APPLY:
      // Apply `<task_val><val>.
      op = task_val;
      POPCONT;
      goto apply;
    case APPLY_T:
      // Apply `<val><task_val>.
      op = val;
      val = task_val;
      POPCONT;
      goto apply;
    case EXIT:
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
      PUSHCONT(EVAL_RIGHT, val->r);
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
      putchar(op->ch);
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
        PUSHCONT(EVAL_RIGHT_S, e2);
        op = op->l;
        goto apply;
      }
    case B2:
      if (op->l->t == D) {
        Cell* e2 = new_cell(AP, op->r, val);
        val = new_cell1(D1, e2);
        break;
      } else {
        PUSHCONT(APPLY, op->l);
        op = op->r;
        goto apply;
      }
    case C2:
      PUSHCONT(APPLY_T, op->r);
      op = op->l;
      goto apply;
    case V2:
      {
        Cell* v = op->l;
        PUSHCONT(APPLY_T, op->r);
        op = val;
        val = v;
        goto apply;
      }
    case S1:
      val = (val->t == K1)
        ? (op->l->t == I ? new_cell1(T1, val->l)
           : op->l->t == T1 ? new_cell(V2, op->l->l, val->l)
           : new_cell(C2, op->l, val->l))
        : new_cell(S2, op->l, val);
      break;
    case B1:
      val = new_cell(B2, op->l, val);
      break;
    case T1:
      {
        Cell* v = op->l;
        op = val;
        val = v;
        goto apply;
      }
    case S:
      val = (val->t == K1)
        ? new_cell1(B1, val->l)
        : new_cell1(S1, val);
      break;
    case V:
      val = op;
      break;
    case D1:
      PUSHCONT(APPLY_T, val);
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
      PUSHCONT(APPLY, val);
      val = new_cell1(CONT, next_cont);
      break;
    case E:
      task = EXIT;
      break;
    case AT:
      current_ch = getchar();
      PUSHCONT(APPLY, val);
      val = new_cell0(current_ch == EOF ? V : I);
      break;
    case QUES:
      PUSHCONT(APPLY, val);
      val = new_cell0(current_ch == op->ch ? I : V);
      break;
    case PIPE:
      PUSHCONT(APPLY, val);
      val = new_cell0(current_ch == EOF ? V : DOT);
      val->ch = current_ch;
      break;
    default:
      errexit("[BUG] apply: invalid operator type %d\n", op->t);
    }
  }
}

// Main ----------------------------------------------------------------

void help(const char *progname) {
  printf("Usage: %s [options] sourcefile\n", progname);
  printf("  -h       print this help and exit\n");
  printf("  -v       print version and exit\n");
  printf("  -v[0-3]  set verbosity level (default: 0)\n");
}

int main(int argc, char *argv[]) {
  char *prog_file = NULL;
  for (int i = 1; i < argc; i++) {
    if (argv[i][0] == '-' && argv[i][1] == 'v' && isdigit(argv[i][2])) {
      verbosity = argv[i][2] - '0';
    } else if (strcmp(argv[i], "-h") == 0) {
      help(argv[0]);
      return 0;
    } else if (strcmp(argv[i], "-v") == 0) {
      printf("Unlambda interpreter " VERSION " by irori\n");
      return 0;
    } else if (argv[i][0] == '-') {
      fprintf(stderr, "bad option %s  (Try -h for more information).\n", argv[i]);
      return 1;
    } else {
      prog_file = argv[i];
    }
  }

  storage_init();
  Cell* root = load_program(prog_file);

  clock_t start = clock();
  run(root);

  if (verbosity >= V_STATS) {
    double evaltime = (clock() - start) / (double)CLOCKS_PER_SEC;
    fprintf(stderr, "  total eval time --- %5.2f sec.\n", evaltime - total_gc_time);
    fprintf(stderr, "  total gc time   --- %5.2f sec.\n", total_gc_time);
    fprintf(stderr, "  major gc count  --- %5d\n", major_gc_count);
    fprintf(stderr, "  minor gc count  --- %5d\n", minor_gc_count);
  }
  return 0;
}
