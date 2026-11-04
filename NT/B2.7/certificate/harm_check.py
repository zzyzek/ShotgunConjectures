# NT-B2.7 / NT-B2.8 recheck.  H(n) = n d(n) / sigma(n) (harmonic mean of
# divisors); n is harmonic when H(n) is an integer.  Factorizations are
# recomputed by trial division and every quantity is computed from them.
#
from fractions import Fraction
from itertools import product
def fac(n):
  f, p = {}, 2
  while p*p <= n:
    while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
    p += 1
  if n > 1: f[n] = f.get(n, 0) + 1
  return f
def sig(f):
  s = 1
  for p, e in f.items(): s *= (p**(e+1) - 1)//(p - 1)
  return s
def dd(f):
  s = 1
  for e in f.values(): s *= e + 1
  return s
def val(f):
  v = 1
  for p, e in f.items(): v *= p**e
  return v
def H(f): return Fraction(val(f)*dd(f), sig(f))
def unitary(f):
  ps = sorted(f)
  for mask in product((0, 1), repeat=len(ps)):
    yield {p: f[p] for p, b in zip(ps, mask) if b}
def harmonic_unitary(f):
  return sorted(val(g) for g in unitary(f) if val(g) > 1 and H(g).denominator == 1)
# B2.7
n = 29495815011600
f = fac(n); print(n, f, "H =", H(f))
hu = harmonic_unitary(f); print("harmonic unitary divisors > 1:", hu)
for m in hu:
  g = fac(m)
  inner = [x for x in harmonic_unitary(g) if x < m]
  print("  ", m, g, "H =", H(g), "smaller harmonic unitary divisors:", inner)
# B2.8
for n in (25075635936512, 12757657068800):
  f = fac(n); h = H(f)
  print(n, f, "H =", h, "sigma mod d =", sig(f) % dd(f), "H | n:", n % int(h) == 0 if h.denominator == 1 else None)
