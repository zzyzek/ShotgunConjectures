# Count nondecreasing sequences of n positive integers with reciprocal sum k
# (A156869), and check T(2n+m, n+m) = T(2n, n) iff m >= 0 on the data range.
from fractions import Fraction as F
from functools import lru_cache
@lru_cache(None)
def cnt(n, r, lo):
  # sequences of length n, entries >= lo, nondecreasing, reciprocal sum r
  if n == 0: return 1 if r == 0 else 0
  if r <= 0: return 0
  if n == 1: return 1 if (r.numerator == 1 and r.denominator >= lo) else 0
  tot = 0; x = max(lo, 1)
  # smallest entry x needs 1/x <= r and n/x >= r
  while F(n, x) >= r:
    if F(1, x) <= r: tot += cnt(n-1, r - F(1, x), x)
    x += 1
  return tot
T = lambda n, k: cnt(n, F(k), 1)
rows = [[T(n, k) for k in range(1, n+1)] for n in range(1, 7)]
print(rows)
data = [1,1,1,3,1,1,14,4,1,1,147,17,4,1,1,3462,164,18,4,1,1]
assert sum(rows, []) == data
for n in range(1, 4):
  for m in range(-(n-1), 4):
    if 2*n+m <= 6:
      e = T(2*n+m, n+m) == T(2*n, n)
      assert e == (m >= 0), (n, m)
print("ok")
