# NT-B16.6 recheck: for non-square, non-prime d <= 430, compute the least
# positive solution (t, u) of t^2 - d u^2 = 1 from the continued fraction of
# sqrt(d) (the convergent at the end of the first period, or of the second
# when the period is odd), and list d with d | u.
#
import sys; sys.path.insert(0, '.')
from math import isqrt
from mr import is_prime
def pell(d):
  a0 = isqrt(d)
  m, q, a = 0, 1, a0
  h0, h1 = 1, a0
  k0, k1 = 0, 1
  while h1*h1 - d*k1*k1 != 1:
    m = q*a - m; q = (d - m*m)//q; a = (a0 + m)//q
    h0, h1 = h1, a*h1 + h0
    k0, k1 = k1, a*k1 + k0
  return h1, k1
hits = []
for d in range(2, 431):
  if isqrt(d)**2 == d or is_prime(d): continue
  t, u = pell(d)
  assert t*t - d*u*u == 1
  if u % d == 0: hits.append((d, t, u))
for h in hits: print(h)
# brute-force minimality for d = 46
t, u = pell(46)
print("46 minimal:", all(isqrt(46*v*v+1)**2 != 46*v*v+1 for v in range(1, u)))
