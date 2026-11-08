/* Divisorial gonality of a multigraph by exhaustive search over effective
   divisors of increasing degree; rank >= 1 tested with Dhar's burning
   algorithm (v-reduced divisors).  Input on stdin: n m k dmax, then m edges
   "a b" (0-based).  The graph is first replaced by sigma_k (every edge a path
   of k edges).  Prints dgon (or "> dmax") and one witness divisor. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N, M, *ea, *eb, *adjstart, *adj, *D0, *D, *cnt, *burnt, *queue;
static long long tested = 0;
static void build(int n, int m, int *a, int *b) {
  int *deg = calloc(n, sizeof(int));
  for (int i = 0; i < m; i++) { deg[a[i]]++; deg[b[i]]++; }
  adjstart = malloc((n + 1) * sizeof(int)); adjstart[0] = 0;
  for (int i = 0; i < n; i++) adjstart[i + 1] = adjstart[i] + deg[i];
  adj = malloc(adjstart[n] * sizeof(int));
  int *pos = malloc(n * sizeof(int)); memcpy(pos, adjstart, n * sizeof(int));
  for (int i = 0; i < m; i++) { adj[pos[a[i]]++] = b[i]; adj[pos[b[i]]++] = a[i]; }
  free(deg); free(pos);
}
/* Is there an effective divisor equivalent to D with a chip on v? D is
   effective; modified in place. */
static int reach(int v) {
  if (D[v] >= 1) return 1;
  for (;;) {
    memset(cnt, 0, N * sizeof(int)); memset(burnt, 0, N * sizeof(int));
    int qh = 0, qt = 0, nb = 1; burnt[v] = 1; queue[qt++] = v;
    while (qh < qt) {
      int u = queue[qh++];
      for (int j = adjstart[u]; j < adjstart[u + 1]; j++) {
        int w = adj[j];
        if (burnt[w]) continue;
        if (++cnt[w] > D[w]) { burnt[w] = 1; queue[qt++] = w; nb++; }
      }
    }
    if (nb == N) return D[v] >= 1;
    for (int u = 0; u < N; u++) if (!burnt[u])
      for (int j = adjstart[u]; j < adjstart[u + 1]; j++)
        if (burnt[adj[j]]) { D[u]--; D[adj[j]]++; }
    if (D[v] >= 1) return 1;
  }
}
static int rank1(void) {
  tested++;
  for (int v = 0; v < N; v++) {
    if (D0[v]) continue;
    memcpy(D, D0, N * sizeof(int));
    if (!reach(v)) return 0;
  }
  return 1;
}
static int sel[64];
static int rec(int i, int start, int d) {
  if (i == d) return rank1();
  for (int x = start; x < N; x++) {
    sel[i] = x; D0[x]++;
    if (rec(i + 1, x, d)) return 1;
    D0[x]--;
  }
  return 0;
}
int main(void) {
  int n, m, k, dmax;
  if (scanf("%d %d %d %d", &n, &m, &k, &dmax) != 4) return 1;
  int *a = malloc(m * sizeof(int)), *b = malloc(m * sizeof(int));
  for (int i = 0; i < m; i++) if (scanf("%d %d", &a[i], &b[i]) != 2) return 1;
  N = n + m * (k - 1); M = m * k;
  ea = malloc(M * sizeof(int)); eb = malloc(M * sizeof(int));
  int e = 0, nv = n;
  for (int i = 0; i < m; i++) {
    int prev = a[i];
    for (int t = 1; t < k; t++) { ea[e] = prev; eb[e] = nv; e++; prev = nv++; }
    ea[e] = prev; eb[e] = b[i]; e++;
  }
  build(N, M, ea, eb);
  D0 = calloc(N, sizeof(int)); D = malloc(N * sizeof(int)); cnt = malloc(N * sizeof(int));
  burnt = malloc(N * sizeof(int)); queue = malloc(N * sizeof(int));
  for (int d = 1; d <= dmax; d++) {
    memset(D0, 0, N * sizeof(int));
    if (rec(0, 0, d)) {
      printf("k=%d N=%d M=%d dgon=%d tested=%lld witness:", k, N, M, d, tested);
      for (int i = 0; i < d; i++) printf(" %d", sel[i]);
      printf("\n"); return 0;
    }
    fprintf(stderr, "k=%d degree %d: none (tested %lld)\n", k, d, tested);
  }
  printf("k=%d N=%d dgon > %d\n", k, N, dmax); return 0;
}
