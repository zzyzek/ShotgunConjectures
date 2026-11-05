# A124431 check (independent of Lean):
#   1. a(n) from the OEIS sum equals the reindexed sum sum_i w(n, i), n < 300;
#   2. the first 60 terms match the printed algebraic g.f.;
#   3. Mathar's recurrence holds for 4 <= n < 300;
#   4. the certificate: F(n, i) = G(n, i+1) - G(n, i) for 4 <= n < 80 and all
#      0 <= i <= n + 2, and G(n, 0) = G(n, n + 2) = 0 for n >= 3.
#
from fractions import Fraction as F
from math import comb
import sympy as sp

N = 300

def C(a, b):
  return comb(a, b) if ( (a >= 0) and (0 <= b) and (b <= a) ) else 0

def a_oeis(n):
  return sum(2 ** k * comb((n + k) // 2, k) * comb((n + k + 1) // 2, k) for k in range(n + 1))

def w(n, i):
  return F(2) ** (n - 2 * i) * (C(n - i, i) ** 2 + 2 * C(n - i, i - 1) * C(n - i + 1, i))

CERT = [((0,0,0,0),(1,4)), ((0,0,0,1),(0,-6)), ((0,1,0,1),(0,-4)), ((0,0,1,0),(-2,-5)),
        ((0,0,2,0),(F(-1,2),0)), ((0,0,3,0),(F(1,2),F(-1,4))), ((1,0,1,0),(1,0)),
        ((1,0,2,0),(0,F(3,4))), ((1,0,3,0),(0,F(-1,2))), ((2,0,2,0),(F(1,4),2)),
        ((2,0,3,0),(0,F(-5,4))), ((3,0,3,0),(F(-1,4),F(1,4)))]

def G(n, i):
  s = sum((u + v * i) * C(n - i - a, i - b) * C(n - i - a2, i - b2) for (a, b, a2, b2), (u, v) in CERT)
  return F(2) ** (n - 2 * i) * s

def c(n):
  return [n + 1, -2 * (2 * n + 1), 2 * (n - 1), 2 * (5 - 2 * n), n - 3]

a  = [a_oeis(n) for n in range(N)]
ok = all(a[n] == sum(w(n, i) for i in range(n + 2)) for n in range(N))
print("1. reindexed sum:", ok)

x  = sp.symbols('x')
q  = 1 - 4 * x + x ** 2
gf = (sp.sqrt((x ** 2 + 1) * q) - q) / (2 * x * q)
co = sp.Poly(sp.series(gf, x, 0, 60).removeO(), x).all_coeffs()[::-1]
ok2 = (co[:60] == a[:60])
print("2. g.f. coefficients (60):", ok2)

ok3 = all(sum(c(n)[l] * a[n - l] for l in range(5)) == 0 for n in range(4, N))
print("3. recurrence 4 <= n <", N, ":", ok3)

ok4 = True
for n in range(4, 80):
  for i in range(n + 3):
    Fni = sum(c(n)[l] * w(n - l, i) for l in range(5))
    ok4 = ok4 and (Fni == G(n, i + 1) - G(n, i))
  ok4 = ok4 and (G(n, 0) == 0) and (G(n, n + 2) == 0)
print("4. certificate:", ok4)
print("ALL OK" if (ok and ok2 and ok3 and ok4) else "FAIL")
