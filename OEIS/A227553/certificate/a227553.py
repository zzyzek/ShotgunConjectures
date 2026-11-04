# A227553: number of solutions of x^2 - y^2 - z^2 = 1 (mod n), versus the
# conjectured values at prime powers.  Counted as sum over z of #{(x,y): x^2 - y^2 = 1 + z^2}.
#
from sympy import primerange
def count(n):
  sq = [0] * n
  for x in range(n): sq[x * x % n] += 1
  diff = [0] * n
  for u in range(n):
    if sq[u]:
      for v in range(n):
        if sq[v]: diff[(u - v) % n] += sq[u] * sq[v]
  return sum(diff[(1 + z * z) % n] for z in range(n))
def conj(p, s):
  if p == 2: return 4 if s == 1 else 2 ** (2 * s - 1)
  return (p + 1) * p ** (2 * s - 1) if p % 4 == 1 else (p - 1) * p ** (2 * s - 1)
bad = []
for p in primerange(2, 60):
  s = 1
  while p ** s <= 1100:
    if count(p ** s) != conj(p, s): bad.append((p, s))
    s += 1
print("prime powers p^s <= 1100 where the conjecture fails:", bad)
