/* Problem O: random-start search for cycles of S -> Z(sum_{a in S} x^a), primes up to ~4000.
   Starts: R random sets of size 1..3; iterate (Brent) to the cycle; report non-standard cycles. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W 64
typedef struct { unsigned long long w[W]; } set;
static int p; static int *pw;
static void step(const set *s, set *t) {
  int el[4100], m = 0;
  memset(t, 0, sizeof(set));
  for (int a = 0; a < p; a++) if ((s->w[a>>6] >> (a&63)) & 1) el[m++] = a;
  for (int b = 0; b < p; b++) { long v = 0; const int *row = pw + (long)b*p;
    for (int i = 0; i < m; i++) v += row[el[i]];
    if (v % p == 0) t->w[b>>6] |= 1ULL << (b&63); }
}
static int cmp(const set *x, const set *y) { return memcmp(x, y, sizeof(set)); }
static set reps[2000]; static int lens[2000], nf;
int main(int argc, char **argv) {
  p = atoi(argv[1]); int R = atoi(argv[2]); srand(p);
  pw = malloc(sizeof(int) * (long)p * p);
  for (int b = 0; b < p; b++) { pw[(long)b*p] = 1; for (int a = 1; a < p; a++) pw[(long)b*p+a] = (int)((long)pw[(long)b*p+a-1] * b % p); }
  for (int r = 0; r < R; r++) {
    set s0; memset(&s0, 0, sizeof s0); int k = 1 + rand() % 3;
    for (int i = 0; i < k; i++) { int a = rand() % p; s0.w[a>>6] |= 1ULL << (a&63); }
    set tort = s0, hare; step(&s0, &hare); int lam = 1, power = 1, steps = 0;
    while (cmp(&tort, &hare)) { if (power == lam) { tort = hare; power *= 2; lam = 0; }
      set h2; step(&hare, &h2); hare = h2; lam++; if (++steps > 100000) { printf("p=%d long\n", p); break; } }
    set rep = hare, cur = hare;
    for (int i = 0; i < lam; i++) { set nx; step(&cur, &nx); cur = nx; if (cmp(&cur, &rep) < 0) rep = cur; }
    int seen = 0; for (int i = 0; i < nf; i++) if (lens[i] == lam && !cmp(&reps[i], &rep)) seen = 1;
    if (!seen && nf < 2000) { reps[nf] = rep; lens[nf] = lam; nf++;
      int sz = 0; for (int a = 0; a < p; a++) sz += (rep.w[a>>6] >> (a&63)) & 1;
      printf("p=%d len=%d size=%d first=", p, lam, sz);
      int c = 0; for (int a = 0; a < p && c < 6; a++) if ((rep.w[a>>6] >> (a&63)) & 1) { printf("%d,", a); c++; }
      printf("\n"); fflush(stdout); }
  }
  printf("p=%d R=%d done cycles=%d\n", p, R, nf);
  return 0;
}
