/*
 * Floating-point screen for periodic billiard orbits in the regular tetrahedron (even length k):
 * DFS over words (first face 0), G = s_{w1}...s_{wk}; axis of the screw motion; start inside T on
 * the axis; simulate k+1 bounces; candidate if the face sequence is w + w[0] and the state after
 * bounce 1 recurs after bounce k+1 (tolerance 1e-9).  Candidates are printed for exact checking.
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static int K;
static double NR[4][3] = {{-1,-1,-1},{-1,1,1},{1,-1,1},{1,1,-1}};
static double L[4][3][3], Tt[4][3];
static int w[64];
static long long leaves = 0, cands = 0;
static double dot(const double *a, const double *b) { return a[0]*b[0]+a[1]*b[1]+a[2]*b[2]; }
static int simulate(double *x, double *u) {
  double xs[3], us[3];
  for (int step = 0; step <= K; step++) {
    int f = w[step % K];
    double best = 1e300; int hit = -1; double second = 1e300;
    for (int i = 0; i < 4; i++) {
      double a = dot(NR[i], u);
      if (a > 1e-12) {
        double s = (1 - dot(NR[i], x))/a;
        if (s < best) { second = best; best = s; hit = i; }
        else if (s < second) { second = s; }
      }
    }
    if ( (hit != f) || (second - best < 1e-9) ) { return 0; }
    for (int r = 0; r < 3; r++) { x[r] += best*u[r]; }
    double c = 2*dot(NR[f], u)/3;
    for (int r = 0; r < 3; r++) { u[r] -= c*NR[f][r]; }
    if (step == 0) { for (int r = 0; r < 3; r++) { xs[r] = x[r]; us[r] = u[r]; } }
  }
  for (int r = 0; r < 3; r++) { if ( (fabs(x[r]-xs[r]) > 1e-7) || (fabs(u[r]-us[r]) > 1e-7) ) { return 0; } }
  return 1;
}
static void leaf(double M[3][3], double t[3]) {
  leaves++;
  double A[3][3];
  for (int r = 0; r < 3; r++) { for (int s = 0; s < 3; s++) { A[r][s] = M[r][s] - (r == s); } }
  /* kernel vector: largest cross product of two rows */
  double u[3] = {0,0,0}, bestn = 0;
  for (int i = 0; i < 3; i++) {
    for (int j = i+1; j < 3; j++) {
      double c[3] = {A[i][1]*A[j][2]-A[i][2]*A[j][1], A[i][2]*A[j][0]-A[i][0]*A[j][2], A[i][0]*A[j][1]-A[i][1]*A[j][0]};
      double nn = dot(c, c);
      if (nn > bestn) { bestn = nn; u[0] = c[0]; u[1] = c[1]; u[2] = c[2]; }
    }
  }
  if (bestn < 1e-20) { return; }
  double nu = sqrt(bestn); for (int r = 0; r < 3; r++) { u[r] /= nu; }
  double tu = dot(t, u);
  if (fabs(tu) < 1e-9) { return; }
  if (tu < 0) { for (int r = 0; r < 3; r++) { u[r] = -u[r]; } tu = -tu; }
  /* axis point: solve (A) p = -(t - tu u) with p.u = 0 via least squares (normal equations) */
  double tp[3]; for (int r = 0; r < 3; r++) { tp[r] = t[r] - tu*u[r]; }
  double B[4][4];
  for (int r = 0; r < 3; r++) { for (int s = 0; s < 3; s++) { B[r][s] = A[r][s]; } B[r][3] = -tp[r]; }
  for (int s = 0; s < 3; s++) { B[3][s] = u[s]; } B[3][3] = 0;
  double N[3][4];
  for (int i = 0; i < 3; i++) { for (int j = 0; j < 4; j++) { double acc = 0; for (int r = 0; r < 4; r++) { acc += B[r][i]*B[r][j]; } N[i][j] = acc; } }
  for (int c = 0; c < 3; c++) {
    int piv = c; for (int r = c+1; r < 3; r++) { if (fabs(N[r][c]) > fabs(N[piv][c])) { piv = r; } }
    for (int j = 0; j < 4; j++) { double tmp = N[c][j]; N[c][j] = N[piv][j]; N[piv][j] = tmp; }
    for (int r = 0; r < 3; r++) { if (r != c) { double f = N[r][c]/N[c][c]; for (int j = 0; j < 4; j++) { N[r][j] -= f*N[c][j]; } } }
  }
  double p[3]; for (int i = 0; i < 3; i++) { p[i] = N[i][3]/N[i][i]; }
  /* chord of the axis inside T */
  double lo = -1e300, hi = 1e300;
  for (int i = 0; i < 4; i++) {
    double a = dot(NR[i], u), b = 1 - dot(NR[i], p);
    if (fabs(a) < 1e-14) { if (b <= 0) { return; } }
    else if (a > 0) { if (b/a < hi) { hi = b/a; } }
    else { if (b/a > lo) { lo = b/a; } }
  }
  if (!(lo < hi - 1e-9)) { return; }
  double s = (lo + hi)/2, x[3] = {p[0]+s*u[0], p[1]+s*u[1], p[2]+s*u[2]}, uu[3] = {u[0], u[1], u[2]};
  if (simulate(x, uu)) {
    cands++;
    for (int i = 0; i < K; i++) { printf("%d", w[i]); }
    printf("\n");
  }
}
static void rec(int k, double M[3][3], double t[3]) {
  if (k == K) { if (w[K-1] != w[0]) { leaf(M, t); } return; }
  for (int f = 0; f < 4; f++) {
    if ( (k == 0) && (f != 0) ) { continue; }
    if ( (k > 0) && (f == w[k-1]) ) { continue; }
    w[k] = f;
    /* G <- G o s_f : M2 = M L_f, t2 = M t_f + t */
    double M2[3][3], t2[3];
    for (int r = 0; r < 3; r++) {
      for (int c = 0; c < 3; c++) { M2[r][c] = M[r][0]*L[f][0][c] + M[r][1]*L[f][1][c] + M[r][2]*L[f][2][c]; }
      t2[r] = M[r][0]*Tt[f][0] + M[r][1]*Tt[f][1] + M[r][2]*Tt[f][2] + t[r];
    }
    rec(k+1, M2, t2);
  }
}
int main(int argc, char **argv) {
  K = atoi(argv[1]);
  for (int f = 0; f < 4; f++) {
    for (int r = 0; r < 3; r++) {
      for (int c = 0; c < 3; c++) { L[f][r][c] = (r == c) - 2.0*NR[f][r]*NR[f][c]/3.0; }
      Tt[f][r] = 2.0*NR[f][r]/3.0;
    }
  }
  double M[3][3] = {{1,0,0},{0,1,0},{0,0,1}}, t[3] = {0,0,0};
  rec(0, M, t);
  fprintf(stderr, "K=%d leaves=%lld candidates=%lld\n", K, leaves, cands);
  return 0;
}
