# A134002/A134003: n(n+5) = a(a+5) + b(b+5) solvable in positive integers
# iff n^2+(n+5)^2 composite.  Check to N by direct search over a.
#
import math, sys
from sympy import isprime
N = int(sys.argv[1])
bad = []
for n in range(1, N + 1):
  T = n * (n + 5)
  sol = False
  a = 1
  while (a * (a + 5) * 2 <= T):
    R = T - a * (a + 5)
    # solve b^2 + 5b - R = 0
    #
    D = 25 + 4 * R
    s = math.isqrt(D)
    if ( (s * s == D) and ((s - 5) % 2 == 0) and (s > 5) ):
      sol = True
      break
    a += 1
  if (sol == isprime(n * n + (n + 5) ** 2)):
    bad.append(n)
print("checked to", N, "mismatches", bad[:20])
