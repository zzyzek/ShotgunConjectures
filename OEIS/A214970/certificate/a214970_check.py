# A214970: n | f(n), f = change of base phi -> phi^2 on the greedy base-phi
# expansion.  Exact arithmetic in Z[phi]: x = p + q*phi stored as (p, q).
# Check the listed terms and L(2k-1), L(2k)+1 for k <= 12.
#
import math
from fractions import Fraction

def mul(x, y):
  # phi^2 = phi + 1
  #
  return (x[0] * y[0] + x[1] * y[1], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])

def val(x):
  # exact sign test via p + q*phi > 0
  #
  return x[0] + x[1] * (1 + math.sqrt(5)) / 2

PHI, IPHI = (0, 1), (-1, 1)

def pw(b, e):
  r = (1, 0)
  base = b if e >= 0 else IPHI
  for _ in range(abs(e)):
    r = mul(r, base)
  return r

def ge(x, y):
  # exact comparison x >= y in Z[phi]: d = p + q phi, compare p >= -q phi
  #
  p, q = x[0] - y[0], x[1] - y[1]
  # p + q*phi >= 0  <=>  2p + q >= -q*sqrt5
  #
  lhs, rq = 2 * p + q, q
  if (rq >= 0):
    return (lhs >= 0) or (lhs * lhs <= 5 * rq * rq)
  return (lhs >= 0) and (lhs * lhs >= 5 * rq * rq)

def greedy(n, lo=-80):
  x, digs = (n, 0), []
  e = 0
  while ge(x, pw(PHI, e + 1)):
    e += 1
  while (e >= lo) and (x != (0, 0)):
    t = pw(PHI, e)
    if ge(x, t):
      x = (x[0] - t[0], x[1] - t[1])
      digs.append(e)
    e -= 1
  assert x == (0, 0), n
  return digs

def f(n):
  s = (0, 0)
  for e in greedy(n):
    t = pw(PHI, 2 * e)
    s = (s[0] + t[0], s[1] + t[1])
  return s

terms = [n for n in range(1, 400) if (f(n)[1] == 0) and (f(n)[0] % n == 0)]
print("terms <400:", terms)
L = [2, 1]
while len(L) < 30:
  L.append(L[-1] + L[-2])
ok = all( (f(L[2*k-1])[1] == 0) and (f(L[2*k-1])[0] % L[2*k-1] == 0) and
          (f(L[2*k]+1)[1] == 0) and (f(L[2*k]+1)[0] % (L[2*k]+1) == 0) for k in range(1, 13) )
print("L(2k-1), L(2k)+1 for k<=12 all terms:", ok)
