/* Enumerate n x n zero-nonzero patterns (arc sets incl. loops) with m arcs, irreducible,
   up to permutation similarity and transposition; print the canonical mask and the term
   counts t_i = number of cycle collections covering exactly i vertices (= monomials of alpha_i). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, N, perm[720][6], np_ = 0;
static void genperm(int *a, int l) {
  if (l == n) { memcpy(perm[np_++], a, sizeof(int)*n); return; }
  for (int i = l; i < n; i++) { int t=a[l]; a[l]=a[i]; a[i]=t; genperm(a, l+1); t=a[l]; a[l]=a[i]; a[i]=t; }
}
static int arc(unsigned long long m, int i, int j) { return (m >> (i*n+j)) & 1; }
static int strong(unsigned long long m) {
  for (int dir = 0; dir < 2; dir++) {
    int seen = 1, ch = 1;
    while (ch) { ch = 0;
      for (int u = 0; u < n; u++) if ((seen>>u)&1) for (int v = 0; v < n; v++)
        if (!((seen>>v)&1) && (dir ? arc(m,v,u) : arc(m,u,v))) { seen |= 1<<v; ch = 1; } }
    if (seen != (1<<n)-1) return 0;
  }
  return 1;
}
static long permcount(unsigned long long m, int S) {
  /* number of permutations of S with all arcs (u, s(u)) in m: DP over subsets of targets */
  int el[6], k = 0; for (int u = 0; u < n; u++) if ((S>>u)&1) el[k++] = u;
  long dp[64]; memset(dp, 0, sizeof dp); dp[0] = 1;
  for (int T = 0; T < (1<<k); T++) { if (!dp[T]) continue; int r = __builtin_popcount(T); if (r == k) continue;
    for (int c = 0; c < k; c++) if (!((T>>c)&1) && arc(m, el[r], el[c])) dp[T|(1<<c)] += dp[T]; }
  return dp[(1<<k)-1];
}
static unsigned long long canon(unsigned long long m) {
  unsigned long long best = ~0ULL;
  for (int p = 0; p < np_; p++) for (int tr = 0; tr < 2; tr++) {
    unsigned long long c = 0;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (arc(m,i,j)) {
      int a = perm[p][i], b = perm[p][j]; if (tr) { int t=a; a=b; b=t; } c |= 1ULL << (a*n+b); }
    if (c < best) best = c;
  }
  return best;
}
int cmpu(const void *a, const void *b) { unsigned long long x=*(unsigned long long*)a, y=*(unsigned long long*)b; return (x>y)-(x<y); }
int main(int argc, char **argv) {
  n = atoi(argv[1]); int m = atoi(argv[2]); int mink = atoi(argv[3]); N = n*n;
  int a[6]; for (int i = 0; i < n; i++) a[i] = i; genperm(a, 0);
  unsigned long long *out = malloc(sizeof(unsigned long long) * 8000000); long no = 0;
  /* iterate m-subsets of N bits (Gosper) */
  unsigned long long v = (1ULL<<m) - 1;
  while (v < (1ULL<<N)) {
    if (strong(v)) {
      long t[7] = {0};
      for (int S = 1; S < (1<<n); S++) t[__builtin_popcount(S)] += permcount(v, S);
      int c2 = 0; for (int i = 1; i <= n; i++) if (t[i] >= 2) c2++;
      if (c2 >= mink) out[no++] = canon(v);
    }
    unsigned long long c = v & -v, r = v + c; v = (((r ^ v) >> 2) / c) | r;
    if (c == 0) break;
  }
  qsort(out, no, sizeof(unsigned long long), cmpu);
  for (long i = 0; i < no; i++) {
    if (i && out[i] == out[i-1]) continue;
    unsigned long long w = out[i]; long t[7] = {0};
    for (int S = 1; S < (1<<n); S++) t[__builtin_popcount(S)] += permcount(w, S);
    printf("%llu", w); for (int k = 1; k <= n; k++) printf(" %ld", t[k]); printf("\n");
  }
  return 0;
}
