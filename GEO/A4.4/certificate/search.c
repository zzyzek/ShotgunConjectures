/*
 * Regular tetrahedron V = (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1); face i is the plane -V_i.x = 1.
 * Reflection in face i: x -> L_i x + t_i with 3 L_i = 3I - 2 n n^T, 3 t_i = 2 n, n = -V_i (integers).
 * DFS over face words w (no immediate repeats, w[last] != w[0]) of length N; keep 3^k * (L_w, t_w)
 * as exact integers (int128).  Report words whose linear part is a reflection (odd N: det -1 and
 * trace 1) or the identity / a rotation of finite... (even N: trace 3), the necessary condition
 * for a periodic orbit of a glide reflection or translation type.
 */
#include <stdio.h>
#include <stdlib.h>
typedef __int128 I;
static int N;
static int V[4][3] = {{1,1,1},{1,-1,-1},{-1,1,-1},{-1,-1,1}};
static I Lm[4][3][3], Tv[4][3];
static int w[64];
static long long hits = 0, total = 0;
static I P3[64];
static void rec(int k, I M[3][3], I t[3]) {
  if (k == N) {
    if (w[N-1] == w[0]) { return; }
    total++;
    I tr = M[0][0] + M[1][1] + M[2][2];
    if (tr == P3[N]) {
      hits++;
      printf("w=");
      for (int i = 0; i < N; i++) { printf("%d", w[i]); }
      printf(" trace=1(*3^N)\n");
    }
    return;
  }
  for (int f = 0; f < 4; f++) {
    if ( (k > 0) && (f == w[k-1]) ) { continue; }
    if ( (k == 0) && (f != 0) ) { continue; }
    w[k] = f;
    I M2[3][3], t2[3];
    for (int r = 0; r < 3; r++) {
      for (int s = 0; s < 3; s++) {
        I acc = 0;
        for (int q = 0; q < 3; q++) { acc += Lm[f][r][q]*M[q][s]; }
        M2[r][s] = acc;
      }
      I acc = 0;
      for (int q = 0; q < 3; q++) { acc += Lm[f][r][q]*t[q]; }
      t2[r] = acc + Tv[f][r]*P3[k];
    }
    rec(k+1, M2, t2);
  }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  P3[0] = 1; for (int i = 1; i < 64; i++) { P3[i] = P3[i-1]*3; }
  for (int f = 0; f < 4; f++) {
    int n[3] = {-V[f][0], -V[f][1], -V[f][2]};
    for (int r = 0; r < 3; r++) {
      for (int s = 0; s < 3; s++) { Lm[f][r][s] = 3*(r == s) - 2*n[r]*n[s]; }
      Tv[f][r] = 2*n[r];
    }
  }
  I M[3][3] = {{1,0,0},{0,1,0},{0,0,1}}, t[3] = {0,0,0};
  rec(0, M, t);
  printf("N=%d words(first face 0)=%lld hits=%lld\n", N, total, hits);
  return 0;
}
