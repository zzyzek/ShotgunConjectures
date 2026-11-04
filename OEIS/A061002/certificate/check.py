# A061002: for primes 5 <= p < 1000,
# denominator(H(p)/H(p-1)) / numerator(H(p-1)/p^2) = p^3.
#
from fractions import Fraction
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
H = Fraction(0); ok = True; Hs = {0: H}
for k in range(1, 1000):
  H += Fraction(1, k); Hs[k] = H
for p in range(5, 1000):
  if not isprime(p): continue
  r = Hs[p] / Hs[p-1]
  s = Hs[p-1] / p**2
  if Fraction(r.denominator, s.numerator) != p**3: ok = False
  if Hs[p-1].numerator % p**2: ok = False
print("ratio = p^3 and p^2 | num H(p-1) for primes 5 <= p < 1000:", ok)
