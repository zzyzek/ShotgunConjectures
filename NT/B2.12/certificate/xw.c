// Search for Erdos "extra-weird" numbers (Guy B2): n with sigma(n) > 3n
// such that there are NOT two disjoint sets of proper divisors of n,
// each summing to n.
//
// Segmented sieve of sigma over [1, N]; every 3-abundant n is factored,
// its proper divisors are listed, and a depth-first search looks for
// set S1 (sum n), then set S2 (sum n) among the unused divisors.
// Prints any n where the search fails (candidate extra-weird), with a
// node budget; prints counts at the end.
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned long long u64;
typedef unsigned __int128 u128;

static u64 dv[100000];
static int nd;
static char used[100000];
static u64 suf[100000];
static long long nodes, budget;

static int cmpdesc(const void *a, const void *b) {
  u64 x = *(const u64*)a, y = *(const u64*)b;
  return (x < y) - (x > y);
}

// Find a subset of unused divisors from index i on with sum t.
// mark: value to write into used[] for chosen elements.
//
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

// Suffix sums of unused divisors.
//
static void mksuf(void) {
  u64 s = 0;
  for (int i = nd-1; i >= 0; i--) {
    if (!used[i]) { s += dv[i]; }
    suf[i] = s;
  }
}

static int primes[200000], np;

int main(int argc, char **argv) {
  u64 N = strtoull(argv[1], 0, 10);
  u64 S = 1 << 20;
  budget = (argc > 2) ? atoll(argv[2]) : 2000000;
  u64 r = (u64)sqrtl((long double)N) + 2;
  char *isc = calloc(r+1, 1);
  for (u64 i = 2; i <= r; i++) {
    if (!isc[i]) {
      primes[np++] = i;
      for (u64 j = i*i; j <= r; j += i) { isc[j] = 1; }
    }
  }
  u64 *sig = malloc(S*8), *rem = malloc(S*8);
  long long cnt3 = 0, fails = 0, bothfail = 0;
  for (u64 L = 1; L <= N; L += S) {
    u64 H = L + S - 1;
    if (H > N) { H = N; }
    for (u64 m = L; m <= H; m++) { sig[m-L] = 1; rem[m-L] = m; }
    for (int k = 0; k < np; k++) {
      u64 p = primes[k];
      if (p*p > H) { break; }
      u64 st = ((L + p - 1)/p)*p;
      for (u64 m = st; m <= H; m += p) {
        u64 pe = 1, s = 1;
        while ((rem[m-L] % p) == 0) { rem[m-L] /= p; pe *= p; s += pe; }
        sig[m-L] *= s;
      }
    }
    for (u64 m = L; m <= H; m++) {
      if (rem[m-L] > 1) { sig[m-L] *= (rem[m-L] + 1); }
      u64 n = m;
      if (sig[m-L] <= 3*n) { continue; }
      cnt3++;
      // Factor n and list divisors.
      //
      u64 pp[64]; int ee[64], nf = 0; u64 x = n;
      for (int k = 0; k < np && (u64)primes[k]*primes[k] <= x; k++) {
        u64 p = primes[k];
        if ((x % p) == 0) { pp[nf] = p; ee[nf] = 0; while ((x % p) == 0) { x /= p; ee[nf]++; } nf++; }
      }
      if (x > 1) { pp[nf] = x; ee[nf] = 1; nf++; }
      nd = 1; dv[0] = 1;
      for (int f = 0; f < nf; f++) {
        int c = nd; u64 pw = 1;
        for (int e = 1; e <= ee[f]; e++) {
          pw *= pp[f];
          for (int j = 0; j < c; j++) { dv[nd++] = dv[j]*pw; }
        }
      }
      qsort(dv, nd, 8, cmpdesc);
      // Drop n itself (dv[0]).
      //
      memmove(dv, dv+1, (nd-1)*8); nd--;
      memset(used, 0, nd);
      mksuf(); nodes = 0;
      int ok = dfs(0, n, 1);
      if (ok) { mksuf(); nodes = 0; ok = dfs(0, n, 2); }
      if (!ok) {
        // Retry: choose S1 starting from smallest-first order is costly;
        // instead try S1 avoiding each of the top divisors in turn.
        //
        for (int ban = 0; (ban < 6) && !ok; ban++) {
          memset(used, 0, nd);
          used[ban] = 3; mksuf(); nodes = 0;
          if (!dfs(0, n, 1)) { continue; }
          used[ban] = 0; mksuf(); nodes = 0;
          ok = dfs(0, n, 2);
        }
      }
      if (!ok) {
        fails++;
        printf("FAIL %llu sigma=%llu nd=%d\n", n, sig[m-L], nd);
        fflush(stdout);
      }
    }
  }
  printf("N=%llu three_abundant=%lld fails=%lld\n", N, cnt3, fails);
  return 0;
}
