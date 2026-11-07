/*
 * Same output as minm.c (k, n(k), least m), but reachable carry sets are kept as lists
 * (stamp array for dedup), so the cost per k is the number of reachable carries, not k.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXD 80
static int64_t K, OFF;
static uint8_t *inL;
static int64_t *L[MAXD+1];
static int64_t len[MAXD+1];
static int32_t *stamp;
static int32_t cur = 0;

static int step(int64_t c, int a, int64_t *nc) {
  int64_t x = K*a + c;
  int64_t r = x & 3;
  int b;
  if      (r == 0) { b = 0; }
  else if (r == 1) { b = 1; }
  else if (r == 3) { b = -1; }
  else             { return 0; }
  *nc = (x - b) >> 2;
  return 1;
}
static int memberL(int64_t c) {
  while (c != 0) {
    int64_t r = c & 3;
    if (r == 2) { return 0; }
    int b = (r == 0 ? 0 : (r == 1 ? 1 : -1));
    c = (c - b) >> 2;
  }
  return 1;
}

int main(int argc, char **argv) {
  int64_t kmin = atoll(argv[1]), kmax = atoll(argv[2]);
  int64_t maxc = kmax/3 + 3, N = 2*maxc + 1;
  OFF = maxc;
  inL = malloc(N); stamp = calloc(N, sizeof(int32_t));
  for (int64_t c = -maxc; c <= maxc; c++) { inL[c+OFF] = memberL(c); }
  for (int i = 0; i <= MAXD; i++) { L[i] = malloc(sizeof(int64_t)*N); }
  int64_t *S = malloc(sizeof(int64_t)*N), *T = malloc(sizeof(int64_t)*N);
  int32_t *mark = calloc(N, sizeof(int32_t)); int32_t mcur = 0;
  for (K = kmin; K <= kmax; K += 2) {
    int n = -1;
    len[0] = 1; L[0][0] = 0;
    for (int i = 0; i < MAXD && n < 0; i++) {
      cur++; len[i+1] = 0;
      for (int64_t j = 0; j < len[i]; j++) {
        int64_t c = L[i][j];
        for (int a = -1; a <= 1; a++) {
          if ( (i == 0) && (a != 1) ) { continue; }
          int64_t nc;
          if (!step(c, a, &nc)) { continue; }
          if (stamp[nc+OFF] != cur) { stamp[nc+OFF] = cur; L[i+1][len[i+1]++] = nc; }
          if ( (a != 0) && inL[nc+OFF] ) { n = i+1; }
        }
      }
    }
    if (n < 0) { printf("%lld none\n", (long long)K); fflush(stdout); continue; }
    unsigned __int128 best = 0; int ok = 0;
    for (int top = -1; top <= 1; top += 2) {
      /* S: allowed carries at depth i+1, marked with mcur */
      int64_t sl = 0; mcur++;
      for (int64_t j = 0; j < len[n]; j++) {
        int64_t c = L[n][j];
        if (inL[c+OFF]) { S[sl++] = c; mark[c+OFF] = mcur; }
      }
      unsigned __int128 lval = 0; int sgn = top, good = 1;
      for (int i = n-1; i >= 0; i--) {
        int order[3];
        if (i == n-1) { order[0] = top; order[1] = 9; order[2] = 9; }
        else          { order[0] = -sgn; order[1] = 0; order[2] = sgn; }
        int chosen = 9; int64_t tl = 0;
        for (int oi = 0; oi < 3 && chosen == 9; oi++) {
          int a = order[oi];
          if (a == 9) { continue; }
          if ( (i == 0) && (a != 1) ) { continue; }
          tl = 0;
          for (int64_t j = 0; j < len[i]; j++) {
            int64_t c = L[i][j], nc;
            if (step(c, a, &nc) && (mark[nc+OFF] == mcur)) { T[tl++] = c; }
          }
          if (tl > 0) { chosen = a; }
        }
        if (chosen == 9) { good = 0; break; }
        mcur++;
        for (int64_t j = 0; j < tl; j++) { mark[T[j]+OFF] = mcur; }
        unsigned __int128 p = 1; for (int j = 0; j < i; j++) { p *= 4; }
        if (chosen*sgn > 0) { lval += p; } else if (chosen*sgn < 0) { lval -= p; }
      }
      if ( good && ( (!ok) || (lval < best) ) ) { best = lval; ok = 1; }
    }
    if (!ok) { printf("%lld %d greedyfail\n", (long long)K, n); }
    else if (n <= 62) { printf("%lld %d %llu\n", (long long)K, n, (unsigned long long)best); }
    else { printf("%lld %d big\n", (long long)K, n); }
  }
  return 0;
}
