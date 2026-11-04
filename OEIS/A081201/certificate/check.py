# A081199-A081201: number of k-subsets of collinear points of {1..k}^n equals
# ((k+2)^n - k^n)/2 (the m-th binomial transform of 0,1,0,1,... is
# ((m+1)^n - (m-1)^n)/2, m = k+1).  Lines are enumerated from point pairs,
# so collinear sets that are not full grid lines would also be counted.
#
from itertools import product, combinations
from math import comb
def count(k, n):
  pts = list(product(range(k), repeat=n))
  lines = set()
  for p, q in combinations(pts, 2):
    d = tuple(b - a for a, b in zip(p, q))
    L = frozenset(r for r in pts if all(
      (r[i] - p[i]) * d[j] == (r[j] - p[j]) * d[i] for i in range(n) for j in range(n)))
    lines.add(L)
  return sum(comb(len(L), k) for L in lines)
def bt(m, n): return sum(comb(n, j) * m**(n - j) for j in range(1, n + 1, 2))
for k, nmax in ((4, 3), (5, 3), (6, 3)):
  print("k =", k, [(n, count(k, n), ((k+2)**n - k**n)//2, bt(k + 1, n)) for n in range(1, nmax + 1)])
