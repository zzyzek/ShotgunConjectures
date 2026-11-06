# Check A097602: definition by running count, the 9-periodic closed form
# st(9k+r), and the conjecture "m^2 is a term iff m mod 3 > 0", for many terms.
#
import math, sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
def issq(v):
  r = math.isqrt(v)
  return r*r == v
a = [None, 1]
c = 1
for n in range(1, N):
  a.append(a[n] + c)
  if issq(a[n+1]): c += 1
def closed(n):
  k, r = divmod(n - 1, 9)
  A, B, C = (3*k+1)**2, (3*k+2)**2, (3*k+3)**2 + 1
  if r < 3:   return A + r*(2*k+1)
  elif r < 6: return B + (r-3)*(2*k+2)
  else:       return C + (r-6)*(2*k+2)
assert all(a[n] == closed(n) for n in range(1, N+1))
sq = set(math.isqrt(v) for v in a[1:] if issq(v))
M = math.isqrt(a[N])
assert all((m in sq) == (m % 3 > 0) for m in range(0, M))
print("ok", N, "terms; m <", M)
