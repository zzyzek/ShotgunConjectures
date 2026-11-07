// Guy C15 (Selfridge): for even m, is the largest zero-sum-free set of
// distinct residues mod m of size floor(sqrt(2m-3))?
//
// Decision search: does a zero-sum-free set of size T exist in Z_m?
// Symmetry: S ~ uS for units u.  Case A: S contains a unit, so WLOG 1 in S.
// Case B: S has no unit; search over non-units only.
// Elements chosen in increasing order; R = set of nonempty subset sums
// (bitset, m <= 256).  x can be added iff x != 0 and -x not in R and x not
// in S (distinct, guaranteed by order).
//
// usage: zsfdec m T   -> prints FOUND set or NONE, with node count.
//
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned long long u64;
static int m, T, W;
static int cand[256], nc;
static int cur[64];
static long long nodes;

typedef struct { u64 w[4]; } bs;

static inline int get(const bs *b, int i) { return (b->w[i >> 6] >> (i & 63)) & 1; }

// r = b rotated by s (i -> i+s mod m).
//
static inline void rot(const bs *b, int s, bs *r) {
  memset(r, 0, sizeof(bs));
  for (int k = 0; k < W; k++) {
    u64 x = b->w[k];
    while (x) {
      int i = (k << 6) + __builtin_ctzll(x);
      x &= x - 1;
      int j = i + s; if (j >= m) { j -= m; }
      r->w[j >> 6] |= 1ULL << (j & 63);
    }
  }
}

static int dfs(int depth, int ci, bs *R) {
  nodes++;
  if (depth == T) { return 1; }
  if ((nc - ci) < (T - depth)) { return 0; }
  for (int k = ci; k < nc; k++) {
    if ((nc - k) < (T - depth)) { return 0; }
    int x = cand[k];
    int t = (m - x) % m;
    if (get(R, t)) { continue; }
    bs nr; rot(R, x, &nr);
    for (int q = 0; q < W; q++) { nr.w[q] |= R->w[q]; }
    nr.w[x >> 6] |= 1ULL << (x & 63);
    cur[depth] = x;
    if (dfs(depth + 1, k + 1, &nr)) { return 1; }
  }
  return 0;
}

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
  m = atoi(argv[1]); T = atoi(argv[2]);
  W = (m + 63) / 64;
  // Case A: 1 in S.
  //
  bs R; memset(&R, 0, sizeof R);
  R.w[0] |= 2ULL;
  cur[0] = 1;
  nc = 0;
  for (int x = 2; x < m; x++) { cand[nc++] = x; }
  nodes = 0;
  int a = dfs(1, 0, &R);
  long long na = nodes;
  if (a) {
    printf("m=%d T=%d FOUND caseA:", m, T);
    for (int i = 0; i < T; i++) { printf(" %d", cur[i]); }
    printf("\n");
    return 0;
  }
  // Case B: no unit in S.
  //
  memset(&R, 0, sizeof R);
  nc = 0;
  for (int x = 1; x < m; x++) { if (gcd(x, m) > 1) { cand[nc++] = x; } }
  nodes = 0;
  int b = dfs(0, 0, &R);
  if (b) {
    printf("m=%d T=%d FOUND caseB:", m, T);
    for (int i = 0; i < T; i++) { printf(" %d", cur[i]); }
    printf("\n");
    return 0;
  }
  printf("m=%d T=%d NONE nodesA=%lld nodesB=%lld\n", m, T, na, nodes);
  return 0;
}
