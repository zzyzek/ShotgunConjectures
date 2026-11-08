# A092967: recompute a(n) = largest prime s+1, s squarefree with prime factors < n, for n <= 23,
# and test "a(n)-1 has prime(n)-1 divisors".
from itertools import combinations
from sympy import isprime, divisor_count, prime, primerange
data = [2,3,7,7,31,31,211,211,211,211,2311,2311,6007,6007,6007,6007,102103,102103,3233231,3233231,3233231,3233231,17160991]
for n in range(1, 24):
  ps = list(primerange(2, n))
  best = 0
  for r in range(len(ps)+1):
    for c in combinations(ps, r):
      s = 1
      for p in c: s *= p
      if isprime(s+1): best = max(best, s+1)
  print(n, best, best == data[n-1], divisor_count(best-1), prime(n)-1, divisor_count(best-1) == prime(n)-1)
