# A135571: n = T(a) - T(b), a > b >= 1, in an odd number of ways, versus the
# conjectured set (square or twice a square or triangular, not square and
# triangular).  Brute force for n <= 20000.
#
from math import isqrt
N = 20000
cnt = [0] * (N + 1)
for b in range(1, N + 1):
  a = b + 1
  while True:
    d = a * (a + 1) // 2 - b * (b + 1) // 2
    if d > N: break
    cnt[d] += 1; a += 1
sq  = lambda n: isqrt(n) ** 2 == n
tri = lambda n: sq(8 * n + 1)
conj = lambda n: (sq(n) or (n % 2 == 0 and sq(n // 2)) or tri(n)) and not (sq(n) and tri(n))
print("mismatches n <= %d:" % N, [n for n in range(1, N + 1) if (cnt[n] % 2 == 1) != conj(n)])
