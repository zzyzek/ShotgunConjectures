# C125 disproof attempt: covering system for k + 2^n with no use of the prime 5,
# then k = 5p (p prime) with 5p + 2^n composite for every n >= 1.
#
import sympy as sp, itertools, sys
from data import isprime
L = int(sys.argv[1]) if len(sys.argv) > 1 else 720
mods = [m for m in sp.divisors(L) if m > 1 and sp.totient(m) <= 64]
avail = {}
for m in mods:
  c = sp.cyclotomic_poly(m, 2)
  ps = [p for p in sp.factorint(int(c)) if sp.n_order(2, p) == m and p != 5]
  if ps: avail[m] = ps
# Greedy covering of Z/L with classes a mod m, one prime per class.
#
unc = set(range(L)); chosen = []; used = {m: 0 for m in avail}
while unc:
  best = None
  for m in avail:
    if used[m] >= len(avail[m]): continue
    for a in range(m):
      cov = sum(1 for r in unc if r % m == a)
      sc = cov / m**0.0
      if best is None or cov > best[0] or (cov == best[0] and m < best[1]): best = (cov, m, a)
  if best is None or best[0] == 0: print('fail', len(unc)); sys.exit(1)
  cov, m, a = best
  p = avail[m][used[m]]; used[m] += 1
  chosen.append((m, a, p)); unc = set(r for r in unc if r % m != a)
print('covering', len(chosen), chosen)
# CRT: k = -2^a mod p for each (m,a,p); k = 5 mod 10.
#
rs = [(-pow(2, a, p)) % p for (m, a, p) in chosen] + [5]
ms = [p for (m, a, p) in chosen] + [10]
k0, M = sp.ntheory.modular.crt(ms, rs)
k0 = int(k0); M = int(M)
print('modulus digits', len(str(M)))
j = 0
while True:
  k = k0 + j*M
  if isprime(k // 5): break
  j += 1
p = k // 5
print('p =', p)
# Verify: for n in one full period 1..L (and beyond, periodic), 5p + 2^n divisible by a covering prime and larger than it.
#
P = [q for (_, _, q) in chosen]
for n in range(1, L + 1):
  v = 5*p + 2**n
  assert any(v % q == 0 and v > q for q in P), n
print('verified: 5p+2^n composite for all n>=1 (period %d)' % L)
