# A228934 check: run the A228929 algorithm (optimal ascending continued
# fraction) on sqrt(44) - 6 in exact Q(sqrt 44) arithmetic, compare with the
# OEIS terms, the conjectured recurrences, and the invariant used in Lean:
# z_(4+2m) = 1/G^2 - 2/G with G = eps^(2^m), eps = 199 + 30 sqrt(44).
#
# Numbers p + q sqrt(44) are pairs of Fractions; signs and rounding are decided
# with mpmath at 4000 digits (the remainders reach about 10^-1300 here).
#
from fractions import Fraction as F
import mpmath
mpmath.mp.dps = 4000

D     = 44
NTERM = 16
OEIS  = [2, 4, 15, -99, -199, -800, -79201, -316808, -12545596801, -50182387208]

def val(z):
  return mpmath.mpf(z[0].numerator) / z[0].denominator + mpmath.mpf(z[1].numerator) / z[1].denominator * mpmath.sqrt(D)

def mul(u, v):
  return (u[0] * v[0] + D * u[1] * v[1], u[0] * v[1] + u[1] * v[0])

def inv(u):
  n = u[0] * u[0] - D * u[1] * u[1]
  return (u[0] / n, -u[1] / n)

# The algorithm: z_0 = x - floor(x), a(k+1) = sign(z_k) round(1/|z_k|),
# z_(k+1) = |z_k| round(1/|z_k|) - 1.
#
z  = (F(-6), F(1))
zs = [z]
a  = [None]
for k in range(NTERM):
  s = 1 if val(z) > 0 else -1
  r = int(mpmath.nint(1 / abs(val(z))))
  frac = 1 / abs(val(z)) - mpmath.floor(1 / abs(val(z)))
  assert abs(frac - mpmath.mpf(1) / 2) > mpmath.mpf(10) ** -10
  a.append(s * r)
  z = (s * z[0] * r - 1, s * z[1] * r)
  zs.append(z)

ok = (a[1:len(OEIS) + 1] == OEIS)
print("terms match OEIS:", ok)

# Conjecture: a(n) < 0 for n >= 4; a(2n) = 4 a(2n-1) - 4 and
# a(2n+1) = -2 a(2n-1)^2 + 1 for n >= 3.
#
ok = ok and all(a[n] < 0 for n in range(4, NTERM + 1))
for n in range(3, (NTERM - 1) // 2 + 1):
  ok = ok and (a[2 * n] == 4 * a[2 * n - 1] - 4) and (a[2 * n + 1] == -2 * a[2 * n - 1] ** 2 + 1)
print("conjecture holds for n <=", NTERM, ":", ok)

# Invariant of the Lean proof, exact in Q(sqrt 44).
#
eps = (F(199), F(30))
G   = eps
for m in range(0, (NTERM - 5) // 2 + 1):
  Gi  = inv(G)
  rhs = (Gi[0] * Gi[0] + D * Gi[1] * Gi[1] - 2 * Gi[0], 2 * Gi[0] * Gi[1] - 2 * Gi[1])
  ok  = ok and (zs[4 + 2 * m] == rhs)
  G   = mul(G, G)
print("invariant z_(4+2m) = 1/G^2 - 2/G:", ok)
print("ALL OK" if ok else "FAIL")
