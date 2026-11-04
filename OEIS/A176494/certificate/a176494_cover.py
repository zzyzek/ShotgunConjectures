# A176494 counterexample: an odd prime p such that |2^m - p| is composite
# for every m >= 1.  Classical covering {3,5,7,13,17,241} of the exponents
# m mod 24: if p == 2^{c_q} (mod q) for classes c_q that cover Z/24, then
# every |2^m - p| has a factor q from the set; it is composite as long as
# it is not q itself, which we rule out directly for small m.
#
import itertools
from sympy import isprime
from sympy.ntheory.modular import crt

Q = [(3, 2), (5, 4), (7, 3), (13, 12), (17, 8), (241, 24)]
M = 1
for q, o in Q: M *= q
best = None
for cs in itertools.product(*[range(o) for q, o in Q]):
  hit = [False] * 24
  for (q, o), c in zip(Q, cs):
    for m in range(c, 24, o): hit[m] = True
  if not all(hit): continue
  r = int(crt([q for q, o in Q], [pow(2, c, q) for (q, o), c in zip(Q, cs)])[0])
  p = r
  while p < 3 or (p % 2 == 0) or not isprime(p):
    p += M
    if best is not None and p > best: break
  if p % 2 and isprime(p) and (best is None or p < best):
    best = p
p = best
print('candidate p =', p)

# Verify: for every m >= 1, |2^m - p| is composite.  For m up to
# bitlen(p)+30 test directly; beyond that |2^m - p| > 241 and the covering
# gives a proper factor (check the covering per residue m mod 24).
#
lim = p.bit_length() + 30
bad = [m for m in range(1, lim + 1) if isprime(abs(2**m - p))]
print('m in [1,%d] with |2^m-p| prime:' % lim, bad)
cov = all(any((pow(2, m, q) - p) % q == 0 for q, o in Q) for m in range(24))
print('every residue m mod 24 covered:', cov)
