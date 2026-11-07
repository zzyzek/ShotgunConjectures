// Enumerate primitive 3-abundant numbers n <= X (sigma(n) > 3n and
// sigma(n/p) <= 3n/p for every prime p | n), optionally odd only, and
// test each for two disjoint sets of proper divisors summing to n.
//
// usage: prim3 X odd(0/1) budget
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned long long u64;
typedef unsigned __int128 u128;

static int primes[2000000], np;
static u64 X;
static long long budget, nodes, cntp = 0, fails = 0, maxnd = 0, incomplete = 0;

static u64 dv[2000000];
static int nd;
static char used[2000000];
static u64 suf[2000000];

static int cmpdesc(const void *a, const void *b) {
  u64 x = *(const u64*)a, y = *(const u64*)b;
  return (x < y) - (x > y);
}

static int dfs(int i, u64 t, char mark) {
  if (t == 0) { return 1; }
  if (++nodes > budget) { return 0; }
  for (; i < nd; i++) {
    if (used[i]) { continue; }
    if (suf[i] < t) { return 0; }
    if (dv[i] <= t) {
      used[i] = mark;
      if (dfs(i+1, t - dv[i], mark)) { return 1; }
      used[i] = 0;
    }
  }
  return 0;
}

static void mksuf(void) {
  u64 s = 0;
  for (int i = nd-1; i >= 0; i--) {
    if (!used[i]) { s += dv[i]; }
    suf[i] = s;
  }
}

static u64 pp[64]; static int ee[64]; static int nf;

static u128 sigpe(u64 p, int e) {
  u128 s = 1, pw = 1;
  for (int i = 0; i < e; i++) { pw *= p; s += pw; }
  return s;
}

static int good(u64 n);
static long long perfect3 = 0;
static void test(u64 n, u128 sg) {
  // Primitive: for each prime p | n, sigma(n/p) <= 3 n/p.
  //
  for (int f = 0; f < nf; f++) {
    u128 s2 = sg / sigpe(pp[f], ee[f]) * sigpe(pp[f], ee[f]-1);
    if (s2 > (u128)3*(n/pp[f])) { return; }
  }
  cntp++;
  if (!good(n)) {
    fails++;
    printf("FAIL %llu =", n);
    for (int f = 0; f < nf; f++) { printf(" %llu^%d", pp[f], ee[f]); }
    printf(" nd=%d\n", nd);
    fflush(stdout);
  }
}

static int good(u64 n) {
  nd = 1; dv[0] = 1;
  for (int f = 0; f < nf; f++) {
    int c = nd; u64 pw = 1;
    for (int e = 1; e <= ee[f]; e++) {
      pw *= pp[f];
      for (int j = 0; j < c; j++) { dv[nd++] = dv[j]*pw; }
    }
  }
  if (nd > maxnd) { maxnd = nd; }
  qsort(dv, nd, 8, cmpdesc);
  memmove(dv, dv+1, (nd-1)*8); nd--;
  memset(used, 0, nd);
  mksuf(); nodes = 0;
  int ok = dfs(0, n, 1);
  if (ok) { mksuf(); nodes = 0; ok = dfs(0, n, 2); }
  for (int ban = 0; (ban < 12) && !ok && (ban < nd); ban++) {
    memset(used, 0, nd);
    used[ban] = 3; mksuf(); nodes = 0;
    if (!dfs(0, n, 1)) { continue; }
    used[ban] = 0; mksuf(); nodes = 0;
    ok = dfs(0, n, 2);
  }
  return ok;
}

// Upper bound on abundancy multiplier from primes with index >= k
// whose product stays <= R.
//
static double maxmult(int k, u64 R) {
  double h = 1.0; u64 prod = 1;
  for (; k < np; k++) {
    u64 p = primes[k];
    if (prod > R / p) { break; }
    prod *= p;
    h *= (double)p / (p - 1);
  }
  return h;
}

static void rec(int k, u64 m, u128 sg) {
  // m has primes with index < k; try adding next prime index j >= k.
  //
  for (int j = k; j < np; j++) {
    u64 q = primes[j];
    if (m > X / q) { return; }
    double h = (double)sg / (double)m;
    if (h * maxmult(j, X / m) <= 3.0 - 1e-12) { return; }
    u64 mm = m; u128 s = 1, pw = 1;
    for (int e = 1; ; e++) {
      if (mm > X / q) { break; }
      mm *= q; pw *= q; s += pw;
      pp[nf] = q; ee[nf] = e; nf++;
      u128 sg2 = sg * s;
      if (sg2 == (u128)3*mm) {
        perfect3++;
        int g = good(mm);
        printf("PERFECT3 %llu good=%d\n", mm, g);
        if (g) { nf--; break; }
      }
      if (sg2 > (u128)3*mm) {
        test(mm, sg2);
        nf--;
        break;
      }
      rec(j+1, mm, sg2);
      nf--;
    }
  }
  if (m <= X / 30000001ULL) { incomplete++; }
}

int main(int argc, char **argv) {
  X = strtoull(argv[1], 0, 10);
  int odd = atoi(argv[2]);
  budget = atoll(argv[3]);
  int L = 30000000;
  char *c = calloc(L+1, 1);
  for (int i = 2; i <= L; i++) {
    if (!c[i]) {
      if (!(odd && i == 2)) { primes[np++] = i; }
      if (np >= 2000000) { break; }
      for (long long j = (long long)i*i; j <= L; j += i) { c[j] = 1; }
    }
  }
  rec(0, 1, 1);
  printf("X=%llu odd=%d primitive3=%lld fails=%lld maxnd=%lld incomplete=%lld perfect3=%lld\n", X, odd, cntp, fails, maxnd, incomplete, perfect3);
  return 0;
}
