/*
 * Forward DRAT checker (RUP + RAT), written for NT-E29.1 so that the
 * UNSAT certificate does not rest on the solver that produced it.
 *
 * Every lemma of the proof is checked in order against the clauses active
 * at that point: RUP means unit propagation on the negated lemma reaches a
 * conflict; RAT (pivot = first literal p) means every active clause D with
 * -p gives a RUP resolvent lemma + (D - {-p}). Deletions remove the
 * matching clause. Accepts only if the empty clause is derived.
 *
 * No backward trimming: every lemma is checked, so the run is slower than
 * drat-trim but the logic is short enough to read.
 *
 * Usage: rupcheck formula.cnf proof.drat   (text DRAT)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int *v; int n, cap; } vec;

static void push(vec *a, int x) {
  if (a->n == a->cap) {
    a->cap = ( a->cap ? (2 * a->cap) : 4 );
    a->v   = realloc(a->v, sizeof(int) * a->cap);
  }
  a->v[a->n++] = x;
}

static int    nvars;
static vec    lits;
static vec    cstart, clen, cdel;
static vec   *watch;
static vec    units;
static signed char *val;
static vec    trail;

static unsigned long long *hkey;
static int   *hnext, *hhead;
static int    hsize = 1 << 22;

static int  lit_index(int l) { return ( (l > 0) ? (2 * l) : (-2 * l + 1) ); }
static int  value(int l) { int v = val[abs(l)]; return ( (l > 0) ? v : -v ); }

static int cmpint(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  return ( (x > y) - (x < y) );
}

/*
 * Order-independent hash of a clause, so deletions can find a clause whose
 * literals the watch scheme has since permuted.
 *
 */
static unsigned long long chash(const int *c, int n) {
  unsigned long long s = 0, x = 0, p = 1;
  int i;
  for (i = 0; i < n; i++) {
    unsigned long long h = (unsigned long long)(c[i] + 1000003LL) * 0x9E3779B97F4A7C15ULL;
    s += h; x ^= (h >> 7); p *= (h | 1);
  }
  return ( s ^ (x * 31) ^ (p * 17) );
}

static int same_clause(int id, const int *c, int n) {
  int i, *a, *b, r;
  if (clen.v[id] != n) { return 0; }
  a = malloc(sizeof(int) * (n + 1)); b = malloc(sizeof(int) * (n + 1));
  memcpy(a, lits.v + cstart.v[id], sizeof(int) * n);
  memcpy(b, c, sizeof(int) * n);
  qsort(a, n, sizeof(int), cmpint); qsort(b, n, sizeof(int), cmpint);
  r = 1;
  for (i = 0; i < n; i++) { if (a[i] != b[i]) { r = 0; break; } }
  free(a); free(b);
  return r;
}

static int add_clause(const int *c, int n) {
  int id = cstart.n, i;
  unsigned long long h = chash(c, n);
  push(&cstart, lits.n); push(&clen, n); push(&cdel, 0);
  for (i = 0; i < n; i++) { push(&lits, c[i]); }
  if (n == 1) { push(&units, id); }
  else if (n >= 2) {
    push(&watch[lit_index(c[0])], id);
    push(&watch[lit_index(c[1])], id);
  }
  hkey = realloc(hkey, sizeof(unsigned long long) * (id + 1));
  hnext = realloc(hnext, sizeof(int) * (id + 1));
  hkey[id] = h; hnext[id] = hhead[h & (hsize - 1)]; hhead[h & (hsize - 1)] = id;
  return id;
}

static int del_clause(const int *c, int n) {
  unsigned long long h = chash(c, n);
  int id;
  for (id = hhead[h & (hsize - 1)]; id >= 0; id = hnext[id]) {
    if ( (!cdel.v[id]) && (hkey[id] == h) && same_clause(id, c, n) ) {
      cdel.v[id] = 1;
      return 1;
    }
  }
  return 0;
}

static void reset(void) {
  int i;
  for (i = 0; i < trail.n; i++) { val[abs(trail.v[i])] = 0; }
  trail.n = 0;
}

static void assign(int l) { val[abs(l)] = ( (l > 0) ? 1 : -1 ); push(&trail, l); }

/*
 * Unit propagation from the current trail plus all active unit clauses.
 * Returns 1 on conflict. Watch lists drop deleted clauses lazily.
 *
 */
static int propagate(int qhead) {
  int i;
  for (i = 0; i < units.n; i++) {
    int id = units.v[i], l;
    if (cdel.v[id]) { continue; }
    l = lits.v[cstart.v[id]];
    if      (value(l) < 0)  { return 1; }
    else if (value(l) == 0) { assign(l); }
  }
  while (qhead < trail.n) {
    int f = -trail.v[qhead++];
    vec *w = &watch[lit_index(f)];
    int j = 0, k;
    for (i = 0; i < w->n; i++) {
      int id = w->v[i], *c, n, found;
      if (cdel.v[id]) { continue; }
      c = lits.v + cstart.v[id]; n = clen.v[id];
      if (c[0] == f) { c[0] = c[1]; c[1] = f; }
      if (value(c[0]) > 0) { w->v[j++] = id; continue; }
      found = 0;
      for (k = 2; k < n; k++) {
        if (value(c[k]) >= 0) {
          c[1] = c[k]; c[k] = f;
          push(&watch[lit_index(c[1])], id);
          found = 1;
          break;
        }
      }
      if (found) { continue; }
      w->v[j++] = id;
      if (value(c[0]) < 0) {
        for (i++; i < w->n; i++) { w->v[j++] = w->v[i]; }
        w->n = j;
        return 1;
      }
      assign(c[0]);
    }
    w->n = j;
  }
  return 0;
}

/*
 * RUP check of the clause c[0..n-1]: assume every literal false. A literal
 * already true under the assumptions (duplicate or tautology) means the
 * clause is trivially implied.
 *
 */
static int rup(const int *c, int n) {
  int i, r;
  reset();
  for (i = 0; i < n; i++) {
    if      (value(c[i]) > 0) { reset(); return 1; }
    else if (value(c[i]) == 0) { assign(-c[i]); }
  }
  r = propagate(0);
  reset();
  return r;
}

static long nrat = 0;

static int rat(const int *c, int n) {
  int p = c[0], id, i, *buf, m, ok = 1;
  if (n == 0) { return 0; }
  buf = malloc(sizeof(int) * (n + nvars + 2));
  for (id = 0; id < cstart.n; id++) {
    int *d = lits.v + cstart.v[id], dn = clen.v[id], has = 0;
    if (cdel.v[id]) { continue; }
    for (i = 0; i < dn; i++) { if (d[i] == -p) { has = 1; break; } }
    if (!has) { continue; }
    m = 0;
    for (i = 0; i < n; i++)  { buf[m++] = c[i]; }
    for (i = 0; i < dn; i++) { if (d[i] != -p) { buf[m++] = d[i]; } }
    if (!rup(buf, m)) { ok = 0; break; }
  }
  free(buf);
  nrat++;
  return ok;
}

static int read_clause(FILE *f, vec *c, int *is_del) {
  int ch, x;
  c->n = 0; *is_del = 0;
  for (;;) {
    ch = fgetc(f);
    if (ch == EOF) { return 0; }
    if ( (ch == ' ') || (ch == '\n') || (ch == '\r') || (ch == '\t') ) { continue; }
    if ( (ch == 'c') || (ch == 'p') ) {
      while ( (ch != '\n') && (ch != EOF) ) { ch = fgetc(f); }
      continue;
    }
    if (ch == 'd') { *is_del = 1; break; }
    ungetc(ch, f);
    break;
  }
  for (;;) {
    if (fscanf(f, "%d", &x) != 1) { return 0; }
    if (x == 0) { return 1; }
    if (abs(x) > nvars) { fprintf(stderr, "variable %d out of range\n", x); exit(2); }
    push(c, x);
  }
}

int main(int argc, char **argv) {
  FILE *fc, *fp;
  vec c = {0};
  int del, i;
  long nlem = 0, ndel = 0, nmiss = 0;
  char line[256];

  if (argc != 3) { fprintf(stderr, "usage: rupcheck formula.cnf proof.drat\n"); return 2; }
  fc = fopen(argv[1], "r"); fp = fopen(argv[2], "r");
  if ( (!fc) || (!fp) ) { fprintf(stderr, "cannot open input\n"); return 2; }

  nvars = 0;
  while (fgets(line, sizeof line, fc)) {
    if (sscanf(line, "p cnf %d", &nvars) == 1) { break; }
  }
  if (nvars <= 0) { fprintf(stderr, "no header\n"); return 2; }
  val   = calloc(nvars + 1, 1);
  watch = calloc(2 * nvars + 2, sizeof(vec));
  hhead = malloc(sizeof(int) * hsize);
  for (i = 0; i < hsize; i++) { hhead[i] = -1; }

  while (read_clause(fc, &c, &del)) { add_clause(c.v, c.n); }
  printf("formula: %d vars, %d clauses\n", nvars, cstart.n);

  while (read_clause(fp, &c, &del)) {
    if (del) {
      if (del_clause(c.v, c.n)) { ndel++; }
      else                      { nmiss++; }
      continue;
    }
    nlem++;
    if ( (!rup(c.v, c.n)) && (!rat(c.v, c.n)) ) {
      printf("FAIL lemma %ld (length %d) is neither RUP nor RAT\n", nlem, c.n);
      return 1;
    }
    if (c.n == 0) {
      printf("VERIFIED: empty clause derived at lemma %ld (%ld RAT checks, %ld deletions, %ld unmatched deletions)\n",
             nlem, nrat, ndel, nmiss);
      return 0;
    }
    add_clause(c.v, c.n);
    if ((nlem % 50000) == 0) { printf("  %ld lemmas checked\n", nlem); fflush(stdout); }
  }
  if (rup(c.v, 0)) {
    printf("VERIFIED: proof ends with %ld lemmas; unit propagation on the final clause set conflicts (%ld RAT checks, %ld deletions, %ld unmatched deletions)\n",
           nlem, nrat, ndel, nmiss);
    return 0;
  }
  printf("FAIL: proof ended without the empty clause (%ld lemmas)\n", nlem);
  return 1;
}
