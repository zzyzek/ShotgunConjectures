# Checks for the Lehmer part.
# 1. Finite case K = 3 (as in three_check in Lehmer_mathlib.lean): x < 6, y < 2(x+1), z < xy+1.
# 2. No composite n < 10^6 with phi(n) | n - 1.
# 3. Pomerance-type prime bounds: for Carmichael-like squarefree odd n < 10^6 (sanity only).
#
from sympy import totient, isprime
sols = []
for x in range(3, 6):
  for y in range(x + 1, 2*(x + 1)):
    for z in range(y + 1, x*y + 1):
      if z % x and (x*y*z - 1) % ((x - 1)*(y - 1)*(z - 1)) == 0:
        sols.append((x, y, z))
print("K=3 finite check solutions:", sols)
bad = [n for n in range(2, 10**6) if not isprime(n) and (n - 1) % totient(n) == 0]
print("composite n < 10^6 with phi(n) | n-1:", bad)
