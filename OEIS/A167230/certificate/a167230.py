# A167230: exp(S)/e for S = Sierpinski triangle (Pascal mod 2).
# (1) S^m(n,k) = m^j, j = popcount(n) - popcount(k), when k AND n == k, else 0
#     (checked exactly for 64x64 and m <= 6);
# (2) exp(S)/e via Dobinski: sum_m m^j/m! / e = Bell(j) (checked numerically).
#
from math import comb, factorial, e
N = 64
S = [[comb(n, k) % 2 for k in range(N)] for n in range(N)]
def mul(A, B):
  return [[sum(A[i][t] * B[t][j] for t in range(j, i + 1)) for j in range(N)] for i in range(N)]
P = [[int(i == j) for j in range(N)] for i in range(N)]
ok = True
for m in range(1, 7):
  P = mul(P, S)
  for n in range(N):
    for k in range(N):
      want = m ** (bin(n).count('1') - bin(k).count('1')) if (k & n) == k else 0
      ok &= (P[n][k] == want)
print("S^m formula for m <= 6, 64x64:", ok)
bell = [1, 1, 2, 5, 15, 52, 203, 877]
print("Dobinski sum_m m^j/m!/e vs Bell(j):",
      all(abs(sum(m**j / factorial(m) for m in range(80)) / e - bell[j]) < 1e-9 for j in range(8)))
