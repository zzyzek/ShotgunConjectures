# OEIS A117414: triangle from Critzer's g.f. (taken as the definition) vs the data, and the
# three conjectured identities: row sums = A000364, column 1 = A024255, column 2 = A117415.
# Exact rational arithmetic, standard library only.
# Run: nice -n 19 python3 check.py
#
from fractions import Fraction as F
from math import factorial, comb

N = 16

# B(n) = (2n)!/2^n = A000680(n); E(z) = Sum z^n / B(n).
#
B = [factorial(2 * n) // 2 ** n for n in range(N + 1)]

# Bivariate series as dict {(n, k): coeff} truncated at z^N.
# E((u-1)z) = Sum_n (u-1)^n z^n / B(n).
#
num = {}
for n in range(N + 1):
  for k in range(n + 1):
    num[(n, k)] = F(comb(n, k) * (-1) ** (n - k), B[n])

# 1/E(-z) as a series in z.
#
em = [F((-1) ** n, B[n]) for n in range(N + 1)]
inv = [F(0)] * (N + 1)
inv[0] = F(1)
for n in range(1, N + 1):
  inv[n] = -sum(em[j] * inv[n - j] for j in range(1, n + 1))

T = [[0] * (n + 1) for n in range(N + 1)]
for n in range(N + 1):
  for k in range(n + 1):
    c = sum(num[(m, k)] * inv[n - m] for m in range(k, n + 1) if (m, k) in num)
    c *= B[n]
    assert c.denominator == 1
    T[n][k] = int(c)

data = [1,0,1,0,4,1,0,48,12,1,0,1088,272,24,1,0,39680,9920,880,40,1,0,2122752,530688,47104,2160,60,1,
        0,156577792,39144448,3474688,159488,4480,84,1,0,15230058496,3807514624,337979392,15514880,436352,8288,112,1]
flat = [x for row in T for x in row]
assert flat[:len(data)] == data
print('g.f. reproduces all', len(data), 'data terms')

# Euler (secant) numbers A000364 and tangent numbers from the e.g.f. recurrences:
# sum_k (-1)^k C(2n,2k) S(k) = 0 for n >= 1 (sec * cos = 1),
# tan = sin * sec gives t(2n-1) = sum_k (-1)^k C(2n-1, 2k+1) S(n-1-k).
#
S = [1]
for n in range(1, N + 1):
  S.append(-sum((-1) ** (n - k) * comb(2 * n, 2 * k) * S[k] for k in range(n)))
assert S[:8] == [1, 1, 5, 61, 1385, 50521, 2702765, 199360981]
tang = {n: sum((-1) ** k * comb(2 * n - 1, 2 * k + 1) * S[n - 1 - k] for k in range(n)) for n in range(1, N + 1)}
assert [tang[n] for n in range(1, 6)] == [1, 2, 16, 272, 7936]

# A117415(n) = (2n)! [x^(2n)] (x tan x - x^2)/8 = (2n)/8 * t(2n-1) - [n == 1] * 2/8.
#
A117415 = [0] + [F(2 * n * tang[n], 8) - (F(2, 8) if n == 1 else 0) for n in range(1, N + 1)]
assert A117415[:8] == [0, 0, 1, 12, 272, 9920, 530688, 39144448]

for n in range(N + 1):
  assert sum(T[n]) == S[n]
  if n >= 1: assert T[n][1] == n * tang[n]
  if n >= 2: assert T[n][2] == A117415[n]
print('rows 0..%d: row sums = A000364, column 1 = n*tangent(2n-1) = A024255, column 2 = A117415' % N)
