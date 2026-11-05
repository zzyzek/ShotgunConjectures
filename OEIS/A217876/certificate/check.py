# A217876 check: the inclusion-exclusion formula
#   T(n,k) = sum_i (-1)^(i+k) C(i,k) C(n-i,i) I(n-2i)
# against brute force over involutions (n <= 10) and the entry's rows, then
# the binomial moments and point probabilities against Poisson(1).
#
# Usage: python3 check.py
#
from math import comb, factorial, exp
from itertools import permutations

NMAX = 3000

I = [1, 1]
for n in range(2, NMAX + 1):
  I.append(I[-1] + (n - 1) * I[-2])

def T(n, k):
  return sum((-1) ** (i + k) * comb(i, k) * comb(n - i, i) * I[n - 2 * i]
             for i in range(0, n + 1) if n - i >= 0)

# Involutions of [n] by number of 2-cycles (i, i+1).
#
def brute(n):
  c = {}
  for p in permutations(range(n)):
    if all(p[p[i]] == i for i in range(n)):
      x    = sum(1 for i in range(n - 1) if p[i] == i + 1)
      c[x] = c.get(x, 0) + 1
  return c

ok = all(brute(n).get(k, 0) == T(n, k) for n in range(0, 11) for k in range(0, n + 1))
print("formula = brute force over involutions, n <= 10:", ok)

rows = [[1], [1], [1, 1], [2, 2], [5, 4, 1], [13, 10, 3], [37, 29, 9, 1],
        [112, 88, 28, 4], [363, 288, 96, 16, 1]]
print("rows 0..8 = entry:", all([T(n, k) for k in range(0, n // 2 + 1)] == rows[n]
                                for n in range(0, 9)))
print("row sums = I(n), n <= 60:", all(sum(T(n, k) for k in range(0, n + 1)) == I[n]
                                       for n in range(0, 61)))

# Lean invariant sqrt(n+1) <= I(n+1)/I(n) <= sqrt(n+1) + 1, in squared form.
#
ok = True
for n in range(0, NMAX):
  a, b = I[n + 1], I[n]
  ok   = ok and (a * a >= (n + 1) * b * b) and ((a - b) * (a - b) <= (n + 1) * b * b)
print("sqrt(n+1) <= I(n+1)/I(n) <= sqrt(n+1)+1, n <", NMAX, ":", ok)

for n in (100, 1000, NMAX):
  bm = [comb(n - i, i) * I[n - 2 * i] / I[n] * factorial(i) for i in range(0, 5)]
  pm = [T(n, j) / I[n] * factorial(j) * exp(1) for j in range(0, 5)]
  print(n, "i! E C(X,i):", [round(v, 4) for v in bm],
        " P(X=j) e j!:", [round(v, 4) for v in pm])
