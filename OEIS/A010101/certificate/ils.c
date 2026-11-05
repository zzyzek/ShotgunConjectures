/*
 * Iterated local search for maximum independent set
 * (Andrade, Resende, Werneck 2012): (1,2)-swaps plus random forced
 * insertions. Reads a DIMACS edge file (duplicates allowed), runs for a
 * time budget, prints every improvement and the best set found.
 *
 * Usage: ils graph.txt seconds seed
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n;
static int **adj, *deg;
static int *in, *tight, *sol, *pos, ssz;
static int *best, bsz;

static unsigned long long rs;
static unsigned rnd(void) {
  rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
  return (unsigned)(rs >> 11);
}

static void add(int v) {
  int i;
  in[v] = 1; pos[v] = ssz; sol[ssz++] = v;
  for (i = 0; i < deg[v]; i++) { tight[adj[v][i]]++; }
}

static void rem(int v) {
  int i, last;
  in[v] = 0; last = sol[--ssz]; sol[pos[v]] = last; pos[last] = pos[v];
  for (i = 0; i < deg[v]; i++) { tight[adj[v][i]]--; }
}

/*
 * Add free vertices, then apply (1,2)-swaps until none applies.
 *
 */
static void local_search(void) {
  int changed = 1, i, j, k, v, x, u, w, *cand, nc;
  cand = malloc(sizeof(int) * n);
  while (changed) {
    changed = 0;
    for (k = 0; k < n; k++) {
      v = rnd() % n;
      if ( (!in[v]) && (tight[v] == 0) ) { add(v); changed = 1; }
    }
    for (v = 0; v < n; v++) {
      if ( (!in[v]) && (tight[v] == 0) ) { add(v); changed = 1; }
    }
    for (i = 0; i < ssz; i++) {
      x = sol[i];
      nc = 0;
      for (j = 0; j < deg[x]; j++) {
        u = adj[x][j];
        if (tight[u] == 1) { cand[nc++] = u; }
      }
      if (nc < 2) { continue; }
      for (j = 0; j < nc; j++) {
        int a = cand[j], b, found = -1, t;
        for (k = j + 1; k < nc; k++) {
          b = cand[k];
          for (t = 0; t < deg[a]; t++) { if (adj[a][t] == b) { break; } }
          if (t == deg[a]) { found = b; break; }
        }
        if (found >= 0) {
          rem(x); add(a); add(found);
          for (t = 0; t < deg[x]; t++) {
            w = adj[x][t];
            if ( (!in[w]) && (tight[w] == 0) ) { add(w); }
          }
          changed = 1;
          break;
        }
      }
      if (changed) { break; }
    }
  }
  free(cand);
}

int main(int argc, char **argv) {
  FILE *f;
  char line[256];
  int a, b, i, m = 0, *ea, *eb, cap = 1 << 20;
  double budget;
  clock_t t0;
  long iter = 0;

  if (argc < 4) { fprintf(stderr, "usage: ils graph seconds seed\n"); return 2; }
  budget = atof(argv[2]); rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[3]) * 2654435761ULL;
  f = fopen(argv[1], "r");
  ea = malloc(sizeof(int) * cap); eb = malloc(sizeof(int) * cap);
  while (fgets(line, sizeof line, f)) {
    if (line[0] == 'p') { sscanf(line, "p edge %d", &n); }
    else if (line[0] == 'e') {
      sscanf(line, "e %d %d", &a, &b);
      if (m == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); }
      ea[m] = a - 1; eb[m] = b - 1; m++;
    }
  }
  deg = calloc(n, sizeof(int)); adj = malloc(sizeof(int *) * n);
  {
    /* Deduplicate edges via an adjacency bitset of the current row. */
    char *seen = calloc((size_t)n * n, 1);
    int *tmpd = calloc(n, sizeof(int));
    for (i = 0; i < m; i++) {
      a = ea[i]; b = eb[i];
      if ( (a == b) || seen[(size_t)a * n + b] ) { continue; }
      seen[(size_t)a * n + b] = seen[(size_t)b * n + a] = 1;
      deg[a]++; deg[b]++;
    }
    for (i = 0; i < n; i++) { adj[i] = malloc(sizeof(int) * (deg[i] + 1)); }
    memset(seen, 0, (size_t)n * n);
    for (i = 0; i < m; i++) {
      a = ea[i]; b = eb[i];
      if ( (a == b) || seen[(size_t)a * n + b] ) { continue; }
      seen[(size_t)a * n + b] = seen[(size_t)b * n + a] = 1;
      adj[a][tmpd[a]++] = b; adj[b][tmpd[b]++] = a;
    }
    free(seen); free(tmpd);
  }
  in = calloc(n, sizeof(int)); tight = calloc(n, sizeof(int));
  sol = malloc(sizeof(int) * n); pos = malloc(sizeof(int) * n); best = malloc(sizeof(int) * n);
  ssz = 0; bsz = 0;
  local_search();
  t0 = clock();
  while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
    int saved = ssz, *save = malloc(sizeof(int) * ssz), k, v, j, force;
    memcpy(save, sol, sizeof(int) * ssz);
    /* Perturb: force 1 (usually) or more random outside vertices in. */
    force = ( (rnd() % (2 * (ssz + 1))) == 0 ) ? (2 + rnd() % 3) : 1;
    for (k = 0; k < force; k++) {
      do { v = rnd() % n; } while (in[v]);
      for (j = 0; j < deg[v]; j++) { if (in[adj[v][j]]) { rem(adj[v][j]); } }
      add(v);
    }
    local_search();
    iter++;
    if (ssz > bsz) {
      bsz = ssz; memcpy(best, sol, sizeof(int) * ssz);
      printf("%.1fs iter %ld size %d\n", (double)(clock() - t0) / CLOCKS_PER_SEC, iter, bsz); fflush(stdout);
    }
    /* Accept worse solutions rarely; otherwise restore. */
    if ( (ssz < saved) && ((rnd() % (1 + ssz)) != 0) ) {
      while (ssz) { rem(sol[0]); }
      for (k = 0; k < saved; k++) { add(save[k]); }
    }
    free(save);
  }
  printf("best %d after %ld iterations\n", bsz, iter);
  for (i = 0; i < bsz; i++) { printf("%d%c", best[i] + 1, (i + 1 < bsz) ? ' ' : '\n'); }
  return 0;
}
