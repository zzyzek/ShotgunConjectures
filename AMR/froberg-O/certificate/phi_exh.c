/* Problem O exhaustive cycle census for prime p <= 31.
   Step 1: Gray-code over all 2^p exponent sets T, maintaining f_T(b) mod p for every b, mark the image
   Z(f_T) in a bitmap.  Every cycle lies in the image.  Step 2: from every image set, iterate phi until a
   repeat (states already finished are skipped via a second bitmap), record each cycle once. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int p, pw[32][32];
static uint32_t phi(uint32_t s) {
  uint32_t u = 0;
  for (int b = 0; b < p; b++) { int v = 0; for (int a = 0; a < p; a++) if ((s >> a) & 1) v += pw[b][a];
    if (v % p == 0) u |= 1u << b; }
  return u;
}
int main(int argc, char **argv) {
  p = atoi(argv[1]);
  for (int b = 0; b < p; b++) { pw[b][0] = 1; for (int a = 1; a < p; a++) pw[b][a] = pw[b][a-1] * b % p; }
  uint64_t N = 1ull << p;
  uint8_t *img = calloc(N / 8, 1), *done = calloc(N / 8, 1);
  int val[32] = {0}; uint32_t T = 0;
  /* T = empty: f = 0, image = all */
  { uint32_t z = (p == 32) ? 0xffffffffu : ((1u << p) - 1); img[z >> 3] |= 1 << (z & 7); }
  for (uint64_t i = 1; i < N; i++) {
    int a = __builtin_ctzll(i);
    if ((T >> a) & 1) { for (int b = 0; b < p; b++) { val[b] -= pw[b][a]; if (val[b] < 0) val[b] += p; } }
    else { for (int b = 0; b < p; b++) { val[b] += pw[b][a]; if (val[b] >= p) val[b] -= p; } }
    T ^= 1u << a;
    uint32_t z = 0; for (int b = 0; b < p; b++) if (val[b] == 0) z |= 1u << b;
    img[z >> 3] |= 1 << (z & 7);
  }
  uint64_t nimg = 0; for (uint64_t s = 0; s < N; s++) if ((img[s >> 3] >> (s & 7)) & 1) nimg++;
  printf("p=%d images=%llu\n", p, (unsigned long long)nimg); fflush(stdout);
  uint32_t path[4096]; long cnt[64] = {0};
  for (uint64_t s0 = 0; s0 < N; s0++) {
    if (!((img[s0 >> 3] >> (s0 & 7)) & 1) || ((done[s0 >> 3] >> (s0 & 7)) & 1)) continue;
    int len = 0; uint32_t s = (uint32_t)s0; int found = -1;
    while (1) {
      if ((done[s >> 3] >> (s & 7)) & 1) break;
      for (int k = 0; k < len; k++) if (path[k] == s) { found = k; break; }
      if (found >= 0) break;
      path[len++] = s; s = phi(s);
      if (len >= 4096) { printf("long path\n"); return 1; }
    }
    if (found >= 0) { int L = len - found; cnt[L < 64 ? L : 63]++;
      printf("p=%d cycle len %d member %x\n", p, L, path[found]); fflush(stdout); }
    for (int k = 0; k < len; k++) done[path[k] >> 3] |= 1 << (path[k] & 7);
  }
  printf("p=%d census:", p); for (int L = 1; L < 64; L++) if (cnt[L]) printf(" len%d:%ld", L, cnt[L]); printf("\n");
  return 0;
}
