/*------------------------------------------------------------------------*/
/* Copyright (C) 2014-2014, Armin Biere, Johannes Kepler University, Linz */
/*------------------------------------------------------------------------*/

#include "druplig.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#include <sys/time.h>
#include <sys/resource.h>

/*------------------------------------------------------------------------*/

#define INC(BYTES) \
do { \
  druplig->stats.mem.cur += (BYTES); \
  if (druplig->stats.mem.max < druplig->stats.mem.cur) \
    druplig->stats.mem.max = druplig->stats.mem.cur; \
} while (0)

#define DEC(BYTES) \
do { \
  assert (druplig->stats.mem.cur >= (BYTES)); \
  druplig->stats.mem.cur -= (BYTES); \
} while (0)

#define NEW(PTR,NUM) \
do { \
  size_t BYTES = sizeof (*(PTR)) * (NUM); \
  (PTR) = druplig->mem.malloc (druplig->mem.state, BYTES); \
  if (!(PTR)) die ("out of memory allocating '%z' bytes", BYTES); \
  memset ((PTR), 0, BYTES); \
  INC (BYTES); \
} while (0)

#define DEL(PTR,NUM) \
do { \
  size_t BYTES = sizeof (*(PTR)) * (NUM); \
  DEC (BYTES); \
  druplig->mem.free (druplig->mem.state, (PTR), BYTES); \
} while (0)

#define RSZ(PTR,OLDNUM,NEWNUM) \
do { \
  size_t OLDBYTES = sizeof (*(PTR)) * (OLDNUM); \
  size_t NEWBYTES = sizeof (*(PTR)) * (NEWNUM); \
  DEC (OLDBYTES); \
  (PTR) = druplig->mem.realloc (druplig->mem.state, \
                                (PTR), OLDBYTES, NEWBYTES); \
  if (!(PTR)) die ("out of memory reallocating '%z' bytes", NEWBYTES); \
  INC (NEWBYTES); \
} while (0)

#define CLEAN(A) \
do { \
  memset (&(A), 0, sizeof (A)); \
} while (0)

/*------------------------------------------------------------------------*/

#define STACK(TYPE) \
struct { TYPE * start; TYPE * top; TYPE * end; }

#define FULL(S)		((S).top == (S).end)
#define EMPTY(S)	((S).top == (S).start)
#define SIZE(S)		((S).end - (S).start)
#define COUNT(S)	((S).top - (S).start)

#define ENLARGE(S) \
do { \
  size_t OLDSIZE = SIZE (S); \
  size_t NEWSIZE = OLDSIZE ? 2*OLDSIZE : 1; \
  size_t OLDCOUNT = COUNT (S); \
  RSZ ((S).start, OLDSIZE, NEWSIZE); \
  (S).top = (S).start + OLDCOUNT; \
  (S).end = (S).start + NEWSIZE; \
} while (0)

#define REL(S) \
do { \
  DEL ((S).start, SIZE (S)); \
  (S).start = (S).top = (S).end = 0; \
} while (0)

#define PUSH(S,E) \
do { \
  if (FULL (S)) ENLARGE (S); \
  *(S).top++ = (E); \
} while (0)

#define POP(S) \
(assert (!EMPTY (S)), *--(S).top)

#define TOP(S) \
(assert (!EMPTY (S)), (S).top[-1])

#define RESET(S) \
do { \
  (S).top = (S).start; \
} while (0)

/*------------------------------------------------------------------------*/

#define LDMAXSIZE 29
#define MAXSIZE ((1 << LDMAXSIZE) - 1)

typedef struct Cls {
#ifndef NDEBUG
  struct Cls * prev, * next;
  long long id;
#endif
#ifndef NSIG
  unsigned long long sig;
#endif
  unsigned size : LDMAXSIZE;
  unsigned garbage : 1;
  unsigned original : 1;
  unsigned inconsistent : 1;
  int lits[1];
} Cls;

typedef STACK(Cls*) Occs;

typedef struct Var { Occs occs[2]; } Var;

typedef struct Stats {
  struct { size_t cur, max; } mem;
  struct {
    struct { struct { long long cur, max; } in, ex; } live;
    struct { long long cur, max, add, del, sat; } orig, red;
    long long id;
  } cls;
  struct { double orig, red, forget, flush, total; } time;
  struct { long long lit, orig, red, forget, flush; } calls;
  long long decisions, propagations;
} Stats;

typedef struct Mem {
  void * state;
  druplig_malloc malloc;
  druplig_realloc realloc;
  druplig_free free;
} Mem;

typedef struct Opts {
  FILE * trace;
  int check, flush, traceorig, die;
} Opts;

typedef struct Limits {
  struct { int interval, countdown; } flush;
} Limits;

typedef struct Timer { double start; double * phase; } Timer;

struct Druplig {
  Mem mem;
  Opts opts;
  Stats stats;
  Timer timer;
  Limits limits;
  int next, flushed, inconsistent;
  STACK(int) clause, trail;
  STACK(unsigned char) marks;
  STACK(signed char) vals;
  STACK(Var) vars;
  Occs empty;
#ifndef NDEBUG
  Cls * first, * last;
#endif
};

/*------------------------------------------------------------------------*/

static void die (const char * fmt, ...) {
  va_list ap;
  fflush (stdout);
  fputs ("*** druplig: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  abort ();
}

/*------------------------------------------------------------------------*/

static double druplig_time (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static void druplig_start (Druplig * druplig, double * phase) {
  assert (!druplig->timer.phase);
  druplig->timer.start = druplig_time ();
  druplig->timer.phase = phase;
}

static void druplig_stop (Druplig * druplig) {
  double time = druplig_time () - druplig->timer.start;
  assert (druplig->timer.phase);
  *druplig->timer.phase += time;
  druplig->timer.phase = 0;
  druplig->stats.time.total += time;
}

#define START(PHASE) \
do { \
  druplig_start (druplig, &druplig->stats.time.PHASE); \
} while (0)

#define STOP() \
do { \
  druplig_stop (druplig); \
} while (0)
   
/*------------------------------------------------------------------------*/

static void * druplig_default_malloc (void * dummy, size_t bytes) {
  (void) dummy;
  return malloc (bytes);
}

static void * druplig_default_realloc (
  void * dummy, void * ptr, size_t old_bytes, size_t new_bytes) {
  (void) dummy, (void) old_bytes;
  return realloc (ptr, new_bytes);
}

static void druplig_default_free ( void * dummy, void * ptr, size_t bytes) {
  (void) dummy, (void) bytes;
  free (ptr);
}

/*------------------------------------------------------------------------*/

void druplig_banner (FILE * file) {
  fprintf (file,
    "c [druplig] Druplig Proof Checker and Tracer Version %s\n",
    VERSION);
}

void druplig_options (Druplig * druplig, FILE * file) {
  fprintf (file,
    "c [druplig] proof checking %s\n",
    druplig->opts.check ? "enabled" : "disabled");
  fprintf (file,
    "c [druplig] flushing satisfied clauses %s%s\n",
    druplig->opts.flush ? "enabled" : "disabled",
    druplig->opts.flush > 1 ? " (eagerly)" : "");
  fprintf (file,
    "c [druplig] dumping DRUP trace to file %s\n",
    druplig->opts.trace ? "enabled" : "disabled");
  fprintf (file,
    "c [druplig] tracing original clauses %s\n",
    druplig->opts.traceorig ? "enabled" : "disabled");
  fprintf (file,
    "c [druplig] abort on failure %s\n",
    druplig->opts.die ? "enabled" : "disabled");
}

/*------------------------------------------------------------------------*/

Druplig * druplig_minit (
  void * state, druplig_malloc m, druplig_realloc r, druplig_free f) {
  Druplig * druplig;
  const char * env;
  size_t bytes;

  assert (!m + !r + !f == 0 || !m + !r + !f == 3);
  if (!m) m = druplig_default_malloc;
  if (!r) r = druplig_default_realloc;
  if (!f) f = druplig_default_free;

  bytes = sizeof *druplig;
  druplig = m (state, bytes);
  if (!druplig) { die ("out of memory allocating Druplig"); return 0; }
  memset (druplig, 0, bytes);
  druplig->mem.state = state;
  druplig->mem.malloc = m;
  druplig->mem.realloc = r;
  druplig->mem.free = f;
  INC (bytes);

  if ((env = getenv ("DRUPLIGTRACE"))) {
    if (!strcmp (env, "stdout")) druplig->opts.trace = stdout;
    else if (!strcmp (env, "stderr")) druplig->opts.trace = stderr;
    else assert (!druplig->opts.trace);
  } else assert (!druplig->opts.trace);

  if ((env = getenv ("DRUPLIGCHECK"))) druplig->opts.check = atoi (env);
  else druplig->opts.check = 1;

  if ((env = getenv ("DRUPLIGFLUSH"))) druplig->opts.flush = atoi (env);
  else druplig->opts.flush = 0;

  if ((env = getenv ("DRUPLIGTRACEORIG")))
    druplig->opts.traceorig = atoi (env);
  else druplig->opts.traceorig = 0;

  if ((env = getenv ("DRUPLIGDIE"))) druplig->opts.die = atoi (env);
  else druplig->opts.die = 1;

  return druplig;
}

Druplig * druplig_init () { return druplig_minit (0, 0, 0, 0); }

/*------------------------------------------------------------------------*/

static int druplig_clean (Druplig * druplig) {
  if (druplig->stats.cls.orig.add) return 0;
  if (druplig->stats.cls.red.add) return 0;
  if (druplig->stats.cls.orig.del) return 0;
  if (druplig->stats.cls.red.del) return 0;
  if (!EMPTY (druplig->clause)) return 0;
  return 1;
}

#define CHECKCLEAN() \
do { \
  if (druplig_clean (druplig)) break; \
  die ("'%s' called after adding literals", __FUNCTION__); \
} while (0)

void druplig_set_check (Druplig * druplig, int check) {
  if (!druplig->opts.check && check && !druplig_clean (druplig))
    die ("can not enable checking after literals have been added");
  druplig->opts.check = check;
}

void druplig_set_flush (Druplig * druplig, int flush) {
  if (!druplig->opts.flush && flush && !druplig_clean (druplig))
    die ("can not enable flushing after literals have been added");
  druplig->opts.flush = flush;
}

/*------------------------------------------------------------------------*/

void druplig_set_trace (Druplig * druplig, FILE * trace) {
  druplig->opts.trace = trace;
}

void druplig_set_traceorig (Druplig * druplig, int val) {
  druplig->opts.traceorig = val;
}

void druplig_set_die (Druplig * druplig, int val) {
  druplig->opts.die = val;
}

/*------------------------------------------------------------------------*/

static void druplig_push_new_var (Druplig * druplig) {
  Var var;
  assert (COUNT (druplig->vars) == COUNT (druplig->vals));
  assert (COUNT (druplig->marks) == COUNT (druplig->marks));
  CLEAN (var);
  PUSH (druplig->vars, var);
  PUSH (druplig->vals, 0);
  PUSH (druplig->marks, 0);
}

void druplig_add_literal (Druplig * druplig, int lit) {
  if (!lit) die ("can not add zero as literal");
  if (lit == INT_MIN) die ("can not add INT_MIN as literal");
  druplig->stats.calls.lit++;
  if (druplig->opts.check) {
    int idx = abs (lit);
    while (COUNT (druplig->vars) <= idx)
      druplig_push_new_var (druplig);
  }
  PUSH (druplig->clause, lit);
}

void druplig_add_literals (Druplig * druplig, int * lits) {
  const int * p;
  int lit;
  for (p = lits; (lit = *p); p++)
    druplig_add_literal (druplig, lit);
}

void druplig_add_literal_args (Druplig * druplig, ...) {
  va_list ap;
  va_start (ap, druplig);
  for (;;) {
    int lit = va_arg (ap, int);
    if (lit) break;
    druplig_add_literal (druplig, lit);
  }
  va_end (ap);
}

/*------------------------------------------------------------------------*/

static int druplig_idx (Druplig * druplig, int lit) {
  int res;
  (void) druplig;
  assert (lit), assert (lit > INT_MIN);
  res = abs (lit);
  assert (res < COUNT (druplig->vars));
  assert (0 < res);
  return res;
}

static Var * druplig_var (Druplig * druplig, int lit) {
  return druplig->vars.start + druplig_idx (druplig, lit);
}

static Occs * druplig_occs (Druplig * druplig, int lit) {
  return druplig_var (druplig, lit)->occs + (lit < 0);
}

static void druplig_connect_literal (Druplig * druplig, Cls * c, int lit) {
  PUSH (*druplig_occs (druplig, lit), c);
}

static size_t druplig_bytes_clause (int size) {
  return sizeof (Cls) + size * sizeof (int);
}

static int druplig_val (Druplig * druplig, int lit) {
  int res = druplig->vals.start[druplig_idx (druplig, lit)];
  if (lit < 0) res = -res;
  return res;
}

static void druplig_assign (Druplig * druplig, int lit) {
  druplig->vals.start[druplig_idx (druplig, lit)] = (lit < 0) ? -1 : 1;
  PUSH (druplig->trail, lit);
}

static void druplig_move_to_front (Druplig * druplig, int * lits) {
  int * p, best = *lits, cand;
  assert (best);
  if (!druplig_val (druplig, best)) return;
  for (p = lits + 1; (cand = *p); p++) {
    if (druplig_val (druplig, cand)) continue;
    *lits = cand, *p = best;
    break;
  }
}

static int druplig_actual (Druplig * druplig, Cls * c) {
  int res = 0, lit;
  const int * p;
  for (p = c->lits; (lit = *p); p++) {
    int val = druplig_val (druplig, lit);
    if (val < 0) continue;
    if (val > 0) res = INT_MAX;
    else if (res < INT_MAX - 1) res++;
  }
  if (c->size) {
    druplig_move_to_front (druplig, c->lits);
    if (c->size > 1) druplig_move_to_front (druplig, c->lits + 1);
  }
  return res;
}

#ifndef NSIG
static unsigned long long druplig_sig (Druplig * druplig) {
  unsigned long long res = 0;
  const int * p;
  for (p = druplig->clause.start; p < druplig->clause.top; p++) {
    int lit = *p;
    unsigned idx = abs (lit);
    unsigned long long tmp = (1ull << ((idx * 1234512347u) & 31));
    if (lit < 0) tmp <<= 32;
    res |= tmp;
  }
  return res;
}
#endif

static void druplig_push_inconsistent (Druplig * druplig, Cls * c) {
  if (!c->inconsistent) {
    assert (!c->inconsistent);
    c->inconsistent = 1;
    druplig->inconsistent++;
    PUSH (druplig->empty, c);
  }
  assert (druplig->inconsistent == COUNT (druplig->empty));
}

static void druplig_remove_occ (Druplig * druplig, Occs * o, Cls * c) {
  Cls ** p;
  (void) druplig;
  for (p = o->start; *p != c; p++)
    assert (p + 1 < o->top);
  while (++p < o->top)
    p[-1] = *p;
  o->top--;
}

static void druplig_remove_inconsistent (Druplig * druplig, Cls * c) {
  assert (c->inconsistent);
  assert (druplig->inconsistent > 0);
  assert (druplig->inconsistent == COUNT (druplig->empty));
  druplig->inconsistent--;
  c->inconsistent = 0;
  druplig_remove_occ (druplig, &druplig->empty, c);
}

static void druplig_inc_internal_live (Druplig * druplig) {
  druplig->stats.cls.live.in.cur++;
  if (druplig->stats.cls.live.in.max < druplig->stats.cls.live.in.cur)
    druplig->stats.cls.live.in.max = druplig->stats.cls.live.in.cur;
}

static Cls * druplig_new_clause (Druplig * druplig) {
  int size, actual, i;
  size_t bytes;
  Cls * res;
  assert (druplig->opts.check);
  druplig_inc_internal_live (druplig);
  size = COUNT (druplig->clause);
  if (size > MAXSIZE)
    die ("clause size %d exceeds maximum size %d", size, MAXSIZE);
  bytes = druplig_bytes_clause (size);
  res = druplig->mem.malloc (druplig->mem.state, bytes);
  if (!res) die ("out of memory allocating clause of size %d", size);
  if (!res) return 0;
  memset (res, 0, bytes);
  INC (bytes);
  for (i = 0; i < size; i++)
    res->lits[i] = druplig->clause.start[i];
  assert (!res->lits[size]);
  res->size = size;
#ifndef NSIG
  res->sig = druplig_sig (druplig);
#endif
  druplig->stats.cls.id++;
#ifndef NDEBUG
  res->id = druplig->stats.cls.id;
#endif
  actual = druplig_actual (druplig, res);
  if (size) {
    druplig_connect_literal (druplig, res, res->lits[0]);
    if (size > 1) druplig_connect_literal (druplig, res, res->lits[1]);
  } 
  if (!actual) druplig_push_inconsistent (druplig, res);
  else if (actual == 1) druplig_assign (druplig, res->lits[0]);
#ifndef NDEBUG
  if (druplig->last) druplig->last->next = res;
  else druplig->first = res;
  res->prev = druplig->last;
  druplig->last = res;
  res->next = 0;
#endif
  return res;
}

static void druplig_trace_clause (Druplig * druplig, const char * prefix) {
  const int * p;
  if (!druplig->opts.trace) return;
  fputs (prefix, druplig->opts.trace);
  for (p = druplig->clause.start; p < druplig->clause.top; p++)
    fprintf (druplig->opts.trace, "%d ", *p);
  fputs ("0\n", druplig->opts.trace);
}

static void druplig_inc_external_live (Druplig * druplig) {
  druplig->stats.cls.live.ex.cur++;
  if (druplig->stats.cls.live.ex.max < druplig->stats.cls.live.ex.cur)
    druplig->stats.cls.live.ex.max = druplig->stats.cls.live.ex.cur;
}

static void druplig_unassign (Druplig * druplig, int lit) {
  signed char * p = druplig->vals.start + druplig_idx (druplig, lit);
  assert (*p);
  *p = 0;
}

static void druplig_backtrack (Druplig * druplig, int level) {
  int count;
  while (COUNT (druplig->trail) > level) {
    int lit = TOP (druplig->trail);
    (void) POP (druplig->trail);
    druplig_unassign (druplig, lit);
  }
  count = COUNT (druplig->trail);
  if (druplig->next > count) druplig->next = count;
}

static int druplig_propagate (Druplig * druplig, int level) {
  while (druplig->next < COUNT (druplig->trail)) {
    int lit = druplig->trail.start[druplig->next++], conflict = 0;
    Occs * o = druplig_occs (druplig, -lit);
    Cls ** p, ** q;
    druplig->stats.propagations++;
    q = o->start;
    for (p = q; p < o->top; p++) {
      int other, valother, * l;
      const int * eolits;
      Cls * c = *p; 
      *q++ = c;
      if (conflict) continue;
      if (c->size == 1) {
	if (!level) druplig_push_inconsistent (druplig, c);
        conflict = 1;
	continue;
      }
      assert (c->size >= 2);
      other = c->lits[0];
      if (other != -lit) c->lits[0] = -lit, c->lits[1] = other;
      else other = c->lits[1];
      assert (c->lits[0] == -lit), assert (c->lits[1] == other);
      valother = druplig_val (druplig, other);
      if (valother > 0) continue;
      eolits = c->lits + c->size;
      for (l = c->lits + 2; l < eolits; l++) 
	if (druplig_val (druplig, *l) >= 0) break;
      if (l < eolits) {
	int replacement = *l;
	c->lits[0] = replacement;
	*l = -lit;
	druplig_connect_literal (druplig, c, replacement);
	q--;
      } else if (!valother) druplig_assign (druplig, other);
      else {
	assert (valother < 0);
	if (!level) druplig_push_inconsistent (druplig, c);
	conflict = 1;
      }
    }
    o->top = q;
    if (conflict) return 0;
  }
  return 1;
}

static void druplig_propagate_after_adding_clause (Druplig * druplig) {
  int ok;
  if (druplig->inconsistent) return;
  if (!EMPTY (druplig->empty)) return;
  ok = druplig_propagate (druplig, 0);
  assert (ok || druplig->inconsistent > 0);
  (void) ok;
}

static void druplig_add_redundant_clause (Druplig * druplig) {
  if (druplig->opts.check) {
    Cls * res = druplig_new_clause (druplig);
    res->original = 0;
  }
  RESET (druplig->clause);
  druplig->stats.cls.red.add++;
  druplig->stats.cls.red.cur++;
  if (druplig->stats.cls.red.max < druplig->stats.cls.red.cur)
    druplig->stats.cls.red.max = druplig->stats.cls.red.cur;
  druplig_inc_external_live (druplig);
  if (druplig->opts.check)
    druplig_propagate_after_adding_clause (druplig);
}

void druplig_add_original_clause (Druplig * druplig) {
  START (orig);
  druplig->stats.calls.orig++;
  if (druplig->opts.traceorig) druplig_trace_clause (druplig, "o ");
  if (druplig->opts.check) {
    Cls * res = druplig_new_clause (druplig);
    res->original = 1;
  }
  RESET (druplig->clause);
  druplig->stats.cls.orig.add++;
  druplig->stats.cls.orig.cur++;
  if (druplig->stats.cls.orig.max < druplig->stats.cls.orig.cur)
    druplig->stats.cls.orig.max = druplig->stats.cls.orig.cur;
  druplig_inc_external_live (druplig);
  if (druplig->opts.check)
    druplig_propagate_after_adding_clause (druplig);
  STOP ();
}

/*------------------------------------------------------------------------*/

static void druplig_delete_clause (Druplig * druplig, Cls * c) {
  size_t bytes = druplig_bytes_clause (c->size);
  DEC (bytes);
  assert (druplig->stats.cls.live.in.cur > 0);
  druplig->stats.cls.live.in.cur--;
  if (c->original) {
    assert (druplig->stats.cls.orig.cur > 0);
    druplig->stats.cls.orig.cur--;
  } else {
    assert (druplig->stats.cls.red.cur > 0);
    druplig->stats.cls.red.cur--;
  }
  if (c->inconsistent) {
    assert (druplig->inconsistent > 0);
    druplig->inconsistent--;
  }
  druplig->mem.free (druplig->mem.state, c, bytes);
}

static void druplig_disconnect_literal (Druplig * druplig, Cls * c, int lit) {
  Occs * o;
  assert (c->size > 0);
  assert (lit == c->lits[0] || (c->size > 1 && lit == c->lits[1]));
  o = druplig_occs (druplig, lit);
  druplig_remove_occ (druplig, o, c);
}

static void druplig_disconnect_clause (Druplig * druplig, Cls * c) {
  if (c->size) {
    druplig_disconnect_literal (druplig, c, c->lits[0]);
    if (c->size > 1) druplig_disconnect_literal (druplig, c, c->lits[1]);
  }
  if (c->inconsistent) druplig_remove_inconsistent (druplig, c);
#ifndef NDEBUG
  if (c->prev) {
    assert (c->prev->next == c);
    c->prev->next = c->next;
  } else {
    assert (druplig->first == c);
    druplig->first = c->next;
  }
  if (c->next) {
    assert (c->next->prev == c);
    c->next->prev = c->prev;
  } else {
    assert (druplig->last == c);
    druplig->last = c->prev;
  }
#endif
}

static void druplig_disconnect_delete_clause (Druplig * druplig, Cls * c) {
  druplig_disconnect_clause (druplig, c);
  druplig_delete_clause (druplig, c);
}

static int druplig_clause_satisfied (Druplig * druplig, Cls * c) {
  const int * p;
  int lit;
  for (p = c->lits; (lit = *p); p++)
    if (druplig_val (druplig, lit) > 0) return 1;
  return 0;
}

static void druplig_flush_satisfied_clauses (Druplig * druplig) {
  int maxidx = COUNT (druplig->vars) - 1, idx, sign;
  assert (druplig->opts.flush);
  assert (druplig->flushed < COUNT (druplig->trail));
  if (druplig->inconsistent) return;
  if (!EMPTY (druplig->empty)) return;
  START (flush);
  druplig->stats.calls.flush++;
  for (idx = 1; idx <= maxidx; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      int i = 0, lit = sign * idx;
      Occs * o = druplig_occs (druplig, lit);
      while (i < COUNT (*o)) {
	Cls * c = o->start[i];
	if (c->lits[0] == lit && druplig_clause_satisfied (druplig, c)) {
	  if (c->original) druplig->stats.cls.orig.sat++;
	  else druplig->stats.cls.red.sat++;
	  druplig_disconnect_delete_clause (druplig, c);
	} else i++;
      }
    }
  }
  for (idx = 1; idx <= maxidx; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      Occs * o = druplig_occs (druplig, sign * idx);
      if (EMPTY (*o)) REL (*o);
    }
  }
  druplig->flushed = COUNT (druplig->trail);

  if (druplig->opts.flush >= 2) druplig->limits.flush.interval = 0;
  if (!druplig->limits.flush.interval) druplig->limits.flush.interval = 1024;
  else if (druplig->limits.flush.interval < (1<<19))
    druplig->limits.flush.interval *= 2;
  else druplig->limits.flush.interval = (1<<19);
  druplig->limits.flush.countdown = druplig->limits.flush.interval;

  STOP ();
}

/*------------------------------------------------------------------------*/

static int druplig_check_redundant_clause (Druplig * druplig) {
  const int * p;
  int ok, level;
  if (!druplig->opts.check) return 1;
  if (druplig->inconsistent) return 1;
  if (!EMPTY (druplig->empty)) return 1;
  assert (druplig->next == COUNT (druplig->trail));
  ok = druplig_propagate (druplig, 0);
  if (!ok) { assert (druplig->inconsistent > 0); return 1; }
  level = COUNT (druplig->trail);
  for (p = druplig->clause.start; ok && p < druplig->clause.top; p++) {
    int lit = -*p, val = druplig_val (druplig, lit);
    if (val > 0) continue;
    if (val < 0) { ok = 0; continue; }
    druplig_assign (druplig, lit);
    druplig->stats.decisions++;
  }
  if (ok) ok = druplig_propagate (druplig, 1);
  assert (!druplig->inconsistent);
  if (ok && druplig->opts.die)
    die ("clause %lld of size %d is not an asymmetric tautology",
      druplig->stats.cls.id+1, (int) COUNT (druplig->clause));
  druplig_backtrack (druplig, level);
  return !ok;
}

static int druplig_need_to_flush_satisfied_clauses (Druplig * druplig) {
  if (!druplig->opts.flush) return 0;
  if (druplig->inconsistent) return 0;
  if (!EMPTY (druplig->empty)) return 0;
  if (druplig->flushed >= COUNT (druplig->trail)) return 0;
  if (!druplig->limits.flush.countdown) return 1;
  druplig->limits.flush.countdown--;
  return 0;
}

int druplig_check_and_add_redundant_clause (Druplig * druplig) {
  int res;
  START (red);
  druplig->stats.calls.red++;
  druplig_trace_clause (druplig, "");
  res = druplig_check_redundant_clause (druplig);
  druplig_add_redundant_clause (druplig);
  STOP ();
  if (res && druplig_need_to_flush_satisfied_clauses (druplig))
    druplig_flush_satisfied_clauses (druplig);
  return res;
}

/*------------------------------------------------------------------------*/

static unsigned char * druplig_mark_ptr (Druplig * druplig, int lit) {
  return druplig->marks.start + druplig_idx (druplig, lit);
}

static void druplig_mark (Druplig * druplig, int lit) {
  unsigned char * p = druplig_mark_ptr (druplig, lit);
  unsigned char bit = 1u << (lit < 0);
  *p |= bit;
}

static int druplig_marked (Druplig * druplig, int lit) {
  unsigned char * p = druplig_mark_ptr (druplig, lit);
  unsigned char bit = 1u << (lit < 0);
  return *p & bit;
}

static void druplig_unmark (Druplig * druplig, int lit) {
  *druplig_mark_ptr (druplig, lit) = 0;
}

static Cls * druplig_find_non_empty_clause (Druplig * druplig) {
#ifndef NSIG
  unsigned long long sig = druplig_sig (druplig);
#endif
  int size = COUNT (druplig->clause);
  Cls * res = 0;
  const int * p;
  assert (size > 0);
#ifndef NDEBUG
  for (p = druplig->clause.start; p < druplig->clause.top; p++)
    assert (!druplig_marked (druplig, *p));
#endif
  for (p = druplig->clause.start; p < druplig->clause.top; p++)
    druplig_mark (druplig, *p);
  for (p = druplig->clause.start; !res && p < druplig->clause.top; p++) {
    int lit = *p;
    Occs * o = druplig_occs (druplig, lit);
    Cls ** q;
    for (q = o->start; !res && q < o->top; q++) {
      const int * l;
      Cls * c = *q;
      int other;
      if (c->size != size) continue;
#ifndef NSIG
      if (c->sig != sig) continue;
#endif
      for (l = c->lits; (other = *l); l++)
	if (!druplig_marked (druplig, other)) break;
      if (!other) res = c;
    }
  }
  for (p = druplig->clause.start; p < druplig->clause.top; p++)
    druplig_unmark (druplig, *p);
  return res;
}

static Cls * druplig_find_empty_clause (Druplig * druplig) {
  Cls ** p, * c;
  assert (EMPTY (druplig->clause));
  for (p = druplig->empty.start; p < druplig->empty.top; p++)
    if (!(c = *p)->size) return c;
  return 0;
}

static Cls * druplig_find_clause (Druplig * druplig) {
  if (EMPTY (druplig->clause)) return druplig_find_empty_clause (druplig);
  else return druplig_find_non_empty_clause (druplig);
}

static int druplig_find_disconnect_delete_clause (Druplig * druplig) {
  int size, res, sat, unsat;
  const int * p;
  if (!druplig->opts.check) return 1;
  sat = 0, unsat = 1;
  for (p = druplig->clause.start; p < druplig->clause.top; p++) {
    int val = druplig_val (druplig, *p);
    if (val >= 0) unsat = 0;
    if (val > 0) sat = 1;
  }
  size = COUNT (druplig->clause);
  if (!druplig->opts.flush || (!sat && !unsat)) {
    Cls * c = druplig_find_clause (druplig);
    if (c) {
      if (c->original) druplig->stats.cls.orig.del++;
      else druplig->stats.cls.red.del++;
      druplig_disconnect_delete_clause (druplig, c);
      res = 1;
    } else res = 0;
  } else res = 1;
  if (!res && druplig->opts.die)
    die ("can not find clause of size %d", size);
  return res;
}

int druplig_forget_clause (Druplig * druplig) {
  int res;
  START (forget);
  druplig->stats.calls.forget++;
  druplig_trace_clause (druplig, "d ");
  res = druplig_find_disconnect_delete_clause (druplig);
  if (res) {
    assert (druplig->stats.cls.live.ex.cur > 0);
    druplig->stats.cls.live.ex.cur--;
  }
  RESET (druplig->clause);
  STOP ();
  return res;
}

/*------------------------------------------------------------------------*/

static double druplig_percent (double a, double b) {
  return b ? 100.0 * a / b : 0;
}

#define PRT(FMT,ARGS...) \
  fprintf (file, "c [druplig] " FMT "\n", ##ARGS)

typedef struct Prof { char * name; long long calls; double time; } Prof;

static int druplig_cmp_prof (const void * p, const void * q) {
  const Prof * a = p, * b = q;
  if (a->time < b->time) return 1;
  if (a->time > b->time) return -1;
  if (a->calls < b->calls) return 1;
  if (a->calls > b->calls) return -1;
  return strcmp (a->name, b->name);
}

#define PROF(NAME,FIELD) \
do { \
  assert (nprof < sizeof prof / sizeof prof[0]); \
  prof[nprof].name = NAME; \
  prof[nprof].calls = s->calls.FIELD; \
  prof[nprof].time = s->time.FIELD; \
  nprof++; \
} while (0)

void druplig_stats (Druplig * druplig, FILE * file) {
  Stats * s = &druplig->stats;
  int nprof = 0, i;
  Prof prof[4];

  long long add = s->cls.orig.add + s->cls.red.add;
  long long del = s->cls.orig.del + s->cls.red.del;

  assert (!druplig->opts.check || s->cls.id == add);

  PRT ("adds: %lld = %lld orig %.0f%% + %lld red %.0f%%",
    add,
    s->cls.orig.add, druplig_percent (s->cls.orig.add, add),
    s->cls.red.add, druplig_percent (s->cls.red.add, add));
  if (druplig->opts.check) {
    PRT ("dels: %lld total %.0f%% = %lld orig %.0f%% + %lld red %.0f%%",
      del, druplig_percent (del, add),
      s->cls.orig.del, druplig_percent (s->cls.orig.del, s->cls.orig.add),
      s->cls.red.del, druplig_percent (s->cls.red.del, s->cls.red.add));
    PRT ("live: %lld internal %.0f%%, %lld orig %.0f%%, %lld red %.0f%%",
      s->cls.live.in.max, druplig_percent (s->cls.live.in.max, add),
      s->cls.orig.max, druplig_percent (s->cls.orig.max, s->cls.orig.add),
      s->cls.red.max, druplig_percent (s->cls.red.max, s->cls.red.add));
    if (druplig->opts.flush)
      PRT ("flsh: %lld orig %.0f%%, %lld red %.0f%%",
	s->cls.orig.sat, druplig_percent (s->cls.orig.sat, s->cls.orig.add),
	s->cls.red.sat, druplig_percent (s->cls.red.sat, s->cls.red.add));
  } else
    PRT ("live: %lld external %.0f%% maximally",
      s->cls.live.ex.max, druplig_percent (s->cls.live.ex.max, add));

  fputs ("c [druplig]\n", file);
  PRT ("%lld decisions, %lld propagations, %lld flushed",
    s->decisions, s->propagations, s->calls.flush);

  fputs ("c [druplig]\n", file);
  PROF("adding original clauses", orig);
  PROF("adding redundant clauses", red);
  PROF("forgetting clauses", forget);
  if (druplig->opts.check && druplig->opts.flush)
    PROF("flushing satisfied clauses", flush);

  qsort (prof, nprof, sizeof prof[0], druplig_cmp_prof);
  for (i = 0; i < nprof; i++)
    PRT ("%10lld calls %8.2f sec %3.0f%% %s",
      prof[i].calls,
      prof[i].time, druplig_percent (prof[i].time, s->time.total),
      prof[i].name);
  fputs ("c [druplig] "
    "-------------------------------------------------------------\n",
    file);
  fprintf (file, "c [druplig] %25.2f sec 100%% in total\n", s->time.total);

  fputs ("c [druplig]\n", file);
  PRT ("%.2f seconds in total, %.1f MB maximally allocated",
    s->time.total, s->mem.max/(double)(1<<20));
}

/*------------------------------------------------------------------------*/

void druplig_reset (Druplig * druplig) {
  int idx, sign;
  REL (druplig->clause);
  REL (druplig->trail);
  while (!EMPTY (druplig->empty)) {
    Cls * c = POP (druplig->empty);
    assert (c->inconsistent);
    if (!c->size) druplig_delete_clause (druplig, c);
  }
  for (idx = 1; idx < COUNT (druplig->vars); idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      Occs * o = druplig_occs (druplig, sign * idx);
      Cls ** p;
      for (p = o->start; p < o->top; p++) {
	Cls * c = *p;
	if (c->garbage || c->size == 1) druplig_delete_clause (druplig, c);
	else c->garbage = 1;
      }
      REL (*o);
    }
  }
  REL (druplig->vars);
  REL (druplig->vals);
  REL (druplig->marks);
  REL (druplig->empty);
  assert (getenv ("DRUPLIGLEAK") ||
          druplig->stats.mem.cur == sizeof *druplig);
  DEL (druplig, 1);
}

/*------------------------------------------------------------------------*/
#ifndef NDEBUG

void druplig_print (Druplig * druplig) {
  Cls * c;
  for (c = druplig->first; c; c = c->next) {
    const int * p;
    printf ("%s(%lld)", (c->original ? "orig" : "red"), c->id);
    for (p = c->lits; *p; p++) printf (" %d", *p);
    printf (" 0\n");
  }
}

#endif
