/* Problem O (Froberg et al. 2018): cycles of S -> Z(sum_{a in S} x^a) on subsets of F_p.
   Start from every subset of size <= K, iterate (Brent) to the cycle, report every distinct
   cycle (identified by its lexicographically smallest member) with its length. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W 16
typedef struct { unsigned long long w[W]; } set;
static int p, pw[1100][1100];
static void step(const set *s, set *t) {
  int a, b, el[1100], m = 0;
  memset(t, 0, sizeof(set));
  for (a = 0; a < p; a++) { if ((s->w[a>>6] >> (a&63)) & 1) { el[m++] = a; } }
  for (b = 0; b < p; b++) {
    long v = 0;
    for (int i = 0; i < m; i++) { v += pw[b][el[i]]; }
    if ((v % p) == 0) { t->w[b>>6] |= 1ULL << (b&63); }
  }
}
static int cmp(const set *x, const set *y) { return memcmp(x, y, sizeof(set)); }
typedef struct { set rep; int len; } cyc;
static cyc found[100000]; static int nf = 0;
static void run(set s0) {
  set pow2 = s0, tort, hare; int lam = 1, power = 1;
  step(&s0, &hare); tort = s0;
  while (cmp(&tort, &hare)) {
    if (power == lam) { tort = hare; power *= 2; lam = 0; }
    set h2; step(&hare, &h2); hare = h2; lam++;
  }
  /* hare is on cycle of length lam; find min rep */
  set rep = hare, cur = hare;
  for (int i = 0; i < lam; i++) { set n; step(&cur, &n); cur = n; if (cmp(&cur, &rep) < 0) { rep = cur; } }
  for (int i = 0; i < nf; i++) { if ((found[i].len == lam) && !cmp(&found[i].rep, &rep)) { return; } }
  found[nf].rep = rep; found[nf].len = lam; nf++;
  printf("p=%d len=%d rep={", p, lam);
  for (int a = 0; a < p; a++) { if ((rep.w[a>>6] >> (a&63)) & 1) { printf(" %d", a); } }
  printf(" }\n"); fflush(stdout);
}
int main(int argc, char **argv) {
  p = atoi(argv[1]); int K = atoi(argv[2]);
  for (int b = 0; b < p; b++) { pw[b][0] = 1; for (int a = 1; a < p; a++) { pw[b][a] = (pw[b][a-1] * b) % p; } }
  int idx[8]; set s;
  for (int k = 0; k <= K; k++) {
    for (int i = 0; i < k; i++) { idx[i] = i; }
    while (1) {
      memset(&s, 0, sizeof s);
      for (int i = 0; i < k; i++) { s.w[idx[i]>>6] |= 1ULL << (idx[i]&63); }
      run(s);
      int i = k - 1;
      while ((i >= 0) && (idx[i] == p - k + i)) { i--; }
      if (i < 0) { break; }
      idx[i]++; for (int j = i + 1; j < k; j++) { idx[j] = idx[j-1] + 1; }
    }
  }
  printf("p=%d K=%d done, %d cycles\n", p, K, nf);
  return 0;
}
