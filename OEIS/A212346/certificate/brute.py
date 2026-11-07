# A212346: a(n) = number of 132-avoiding permutations of 1..n in which no entry has
# 4 or more larger entries to its left (coefficient of x^0 in Q_{n,132}^{(0,4,0,0)}(x)).
# Checks brute force (n <= 10) = recursion N_k(n) = sum_{i<n} N_k(i) N_{k-1-i}(n-1-i)
# = OEIS data = (n+3)(n^2-4)/6 for n >= 3 (recursion up to n = 35).
import sys
from itertools import permutations, combinations
from functools import lru_cache
DATA = [1,1,2,5,14,28,48,75,110,154,208,273,350,440,544,663,798,950,1120,1309,1518,1748,
        2000,2275,2574,2898,3248,3625,4030,4464,4928,5423,5950,6510,7104,7733]
def avoids132(p):
  n = len(p)
  for i in range(n):
    for j in range(i+1, n):
      if p[j] > p[i]:
        for k in range(j+1, n):
          if p[i] < p[k] < p[j]: return False
  return True
def ok(p, k):
  return all(sum(1 for j in range(i) if p[j] > p[i]) < k for i in range(len(p)))
@lru_cache(None)
def N(k, n):
  if n == 0: return 1
  if k <= 0: return 0
  return sum(N(k, i) * N(k-1-i, n-1-i) for i in range(n))
bad = 0
for n in range(0, 11):
  b = sum(1 for p in permutations(range(n)) if avoids132(p) and ok(p, 4))
  if b != N(4, n): bad += 1; print("brute", n, b, N(4, n))
for n in range(36):
  if N(4, n) != DATA[n]: bad += 1; print("data", n)
  if n >= 3 and 6*N(4, n) != (n+3)*(n*n-4): bad += 1; print("formula", n)
print("failures:", bad); sys.exit(1 if bad else 0)
