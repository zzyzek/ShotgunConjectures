/* A216368: T(n,k) = number of distinct k-th derivatives at x = 1 of the functions given by
 * power towers of n x's (= rooted trees with n nodes: a node is x raised to the product of its
 * children's functions).  Derivative vectors f^(j)(1), j <= N, are computed modulo a prime P via
 * f = exp(g log x): u = g*log (Leibniz), f^(k+1) = sum_j C(k,j) u^(j+1) f^(k-j).
 * Distinct residues certify distinct integers, so (#distinct residues) <= T(n,k), with equality
 * when no two true values coincide mod P; T(n,n) = A000081(n) is certified when the count of
 * distinct residues of the n-th derivative equals the number of trees.
 * Usage: towers N P   (prints, for n = 1..N, #trees and #distinct residues of f^(k)(1), k = 1..n)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static int N; static u64 P; static u64 C[40][40], LG[40];
static u64 *D; static int *sz; static long ntree = 0, cap = 0;
static long startS[40], endS[40];
static u64 mulm(u64 a, u64 b) { return (u64)((u128)a * b % P); }
static void times(const u64 *a, const u64 *b, u64 *r) {
  for (int k = 0; k <= N; k++) { u128 s = 0; for (int j = 0; j <= k; j++) { s += (u128)mulm(C[k][j], mulm(a[j], b[k - j])); } r[k] = (u64)(s % P); } }
static void powx(const u64 *g, u64 *f) {
  u64 u[40]; times(g, LG, u); f[0] = 1;
  for (int k = 0; k < N; k++) { u128 s = 0; for (int j = 0; j <= k; j++) { s += (u128)mulm(C[k][j], mulm(u[j + 1], f[k - j])); } f[k + 1] = (u64)(s % P); } }
static int target; static u64 *out; static long nout;
static void dfs(int rem, long imin, const u64 *g) {
  if (rem == 0) { u64 f[40]; powx(g, f); memcpy(out + nout * (N + 1), f, sizeof(u64) * (N + 1)); nout++; return; }
  for (long i = imin; i < ntree && sz[i] <= rem; i++) { u64 h[40]; times(g, D + i * (N + 1), h); dfs(rem - sz[i], i, h); } }
static int cmpk; static int cmp(const void *a, const void *b) { u64 x = ((const u64 *)a)[0], y = ((const u64 *)b)[0]; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
  N = atoi(argv[1]); P = strtoull(argv[2], 0, 10);
  for (int i = 0; i < 40; i++) { C[i][0] = 1 % P; for (int j = 1; j <= i; j++) C[i][j] = (C[i - 1][j - 1] + (j < i ? C[i - 1][j] : 0)) % P; }
  /* log x at 1: L[0] = 0, L[k] = (-1)^(k-1) (k-1)! */
  u64 fact = 1; LG[0] = 0; for (int k = 1; k <= N; k++) { LG[k] = (k % 2) ? fact : (P - fact) % P; fact = mulm(fact, k); }
  cap = (N >= 19) ? 2800000 : 1100000; D = malloc(sizeof(u64) * (N + 1) * cap); sz = malloc(sizeof(int) * cap);
  long outcap = (N >= 19) ? 4800000 : 2000000; out = malloc(sizeof(u64) * (N + 1) * outcap); u64 *keys = malloc(sizeof(u64) * outcap);
  for (int n = 1; n <= N; n++) {
    u64 one[40] = {0}; one[0] = 1;
    nout = 0; dfs(n - 1, 0, one);
    printf("n=%d trees=%ld distinct:", n, nout);
    for (int k = 1; k <= n; k++) { for (long t = 0; t < nout; t++) keys[t] = out[t * (N + 1) + k]; qsort(keys, nout, sizeof(u64), cmp); long d = nout ? 1 : 0; for (long t = 1; t < nout; t++) if (keys[t] != keys[t - 1]) d++; printf(" %ld", d); }
    printf("\n"); fflush(stdout);
    if (n < N) { startS[n] = ntree; for (long t = 0; t < nout; t++) { if (ntree >= cap) { fprintf(stderr, "cap\n"); return 1; } memcpy(D + ntree * (N + 1), out + t * (N + 1), sizeof(u64) * (N + 1)); sz[ntree] = n; ntree++; } endS[n] = ntree; }
  }
  return 0; }
