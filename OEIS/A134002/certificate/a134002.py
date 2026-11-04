# A134002/A134003: n(n+5) = a(a+5) + b(b+5) solvable in positive integers
# iff M = n^2 + (n+5)^2 is composite.  Brute force for n <= 3000.
#
from sympy import isprime
from math import isqrt
def solvable(n):
  T = n * (n + 5)
  for a in range(1, n):
    r = T - a * (a + 5)
    if r < 6: break
    # b(b+5) = r  <=>  (2b+5)^2 = 4r + 25
    s = isqrt(4 * r + 25)
    if s * s == 4 * r + 25 and s > 5 and (s - 5) % 2 == 0: return True
  return False
bad = [n for n in range(1, 3001) if solvable(n) == isprime(n*n + (n+5)**2)]
print("n <= 3000 where solvability != compositeness of M:", bad)
