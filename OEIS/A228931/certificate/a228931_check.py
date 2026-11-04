# A228929 algorithm ("optimal ascending continued fraction"):
# z0 = x - floor(x); a(n) = sign(z_n) round(1/|z_n|); z_{n+1} = |z_n| round(1/|z_n|) - 1.
# Exact arithmetic in Q(sqrt D) (z = p + q sqrt D), rounding via mpmath.
#
from fractions import Fraction as F
import mpmath
mpmath.mp.dps = 3000

def run(D, p0, q0, N):
  p, q = F(p0), F(q0)
  out = []
  for _ in range(N):
    z = mpmath.mpf(p.numerator) / p.denominator + mpmath.mpf(q.numerator) / q.denominator * mpmath.sqrt(D)
    s = 1 if z > 0 else -1
    r = int(mpmath.nint(1 / abs(z)))
    out.append((s * r, (s * p, s * q)))
    p, q = s * p * r - 1, s * q * r
  return out

for name, D, p0, q0 in [("A228931 sqrt2-1", 2, -1, 1), ("A228933 1/phi", 5, F(-1, 2), F(1, 2)),
                        ("A228934 sqrt44-6", 44, -6, 1)]:
  res = run(D, p0, q0, 10)
  print(name, [a for a, _ in res])
  for a, (p, q) in res[:8]:
    # print |z| and its inverse 1/|z| = (p - q sqrtD)/(p^2 - D q^2)
    #
    n = p * p - D * q * q
    print("   a=%d  |z| = %s + %s*sqrt(%d)   1/|z| = %s + %s*sqrt(%d)" % (a, p, q, D, p / n, -q / n, D))
