# A188644-A188647 in exact Z[sqrt D] arithmetic, D = x^2 + y, y = +-1:
# k = (sqrt D + x)^2 = (2x^2+y) + 2x sqrt D, 1/k = conjugate.
# Check (k^n + k^-n)/2 = T_n(2x^2+y) (integer) and
# a(n) = a(n-1) k - (k-1)/k^n, a(0) = 1, equals (k^{n+1} + k^-n)/(k+1) and is an integer.
#
from fractions import Fraction as Fr
def mul(u, v, D): return (u[0]*v[0] + D*u[1]*v[1], u[0]*v[1] + u[1]*v[0])
def inv(u, D):
  nrm = u[0]*u[0] - D*u[1]*u[1]
  return (Fr(u[0], nrm), Fr(-u[1], nrm))
ok1 = ok2 = True
for y in (-1, 1):
  for x in range(1, 9):
    D = x*x + y
    k = (2*x*x + y, 2*x); ki = inv(k, D)
    assert mul(k, ki, D) == (1, 0)
    m = 2*x*x + y
    T = [1, m]
    while len(T) < 25: T.append(2*m*T[-1] - T[-2])
    p, q = (1, 0), (1, 0)
    a = (Fr(1), Fr(0))
    for n in range(0, 24):
      s = (p[0] + q[0], p[1] + q[1])
      ok1 &= (s[1] == 0 and s[0] == 2*T[n])
      if n >= 1:
        km1 = (k[0] - 1, k[1])
        t = mul(km1, q, D)
        a = (mul(a, k, D)[0] - t[0], mul(a, k, D)[1] - t[1])
        ok2 &= (a[1] == 0 and a[0].denominator == 1)
      p, q = mul(p, k, D), mul(q, ki, D)
print("(k^n + k^-n)/2 = T_n(2x^2+y) in Z, x <= 8, n < 24:", ok1)
print("A188646/7 recurrence values are integers, x <= 8, n < 24:", ok2)
