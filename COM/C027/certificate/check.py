# Self-contained check (second reader, 2026-11-01). Standard library only.
# Run: nice -n 19 python3 check.py   (data file: see DATA.md at the repo root)
#
import math, os, sys
DATA = os.environ.get('PSP_DATA',
  os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'data', 'psp2-annot-below-1e13.txt'))

def isprime(n):
  if n < 2: return False
  for p in (2,3,5,7,11,13,17,19,23,29,31,37):
    if n % p == 0: return n == p
  d, s = n - 1, 0
  while d % 2 == 0: d //= 2; s += 1
  for a in (2,3,5,7,11,13,17,19,23,29,31,37):
    x = pow(a, d, n)
    if x in (1, n - 1): continue
    for _ in range(s - 1):
      x = x * x % n
      if x == n - 1: break
    else: return False
  return True

def factor(n):
  # trial division then Pollard rho; returns sorted prime list with multiplicity
  fs = []
  for p in range(2, 10000):
    while n % p == 0: fs.append(p); n //= p
    if p * p > n: break
  def rho(n):
    if n % 2 == 0: return 2
    for c in range(1, 100):
      x = y = 2; d = 1
      while d == 1:
        x = (x * x + c) % n; y = (y * y + c) % n; y = (y * y + c) % n
        d = math.gcd(abs(x - y), n)
      if d != n: return d
  stack = [n] if n > 1 else []
  while stack:
    m = stack.pop()
    if isprime(m): fs.append(m); continue
    d = rho(m); stack += [d, m // d]
  return sorted(fs)

def poulet(n):
  return n > 2 and not isprime(n) and pow(2, n - 1, n) == 1

def carmichael(n):
  # Korselt: squarefree, composite, p-1 | n-1 for every prime p | n
  fs = factor(n)
  return (len(fs) >= 2 and len(set(fs)) == len(fs) and
          all((n - 1) % (p - 1) == 0 for p in fs))

def load(limit=10**13):
  # (n, prime factors with multiplicity, is_carmichael) for base-2 psp below limit
  out = []
  for line in open(DATA):
    parts = line[2:].split()
    n = int(parts[0])
    if n >= limit: continue
    out.append((n, [int(x) for x in parts[1:]], line[0] == 'C'))
  return out

def digsum(n): return sum(map(int, str(n)))

def divisors(n):
  ds = [1]
  for p in sorted(set(factor(n))):
    e = factor(n).count(p)
    ds = [d * p ** i for d in ds for i in range(e + 1)]
  return sorted(ds)

def carmichael_compatible(r, m):
  # Larsen, arXiv:2504.09056v2, definition before Theorem 1: g = (r, m), h = (lambda(g), m);
  # incompatible iff (g, 2 phi(g)) > 1, or h does not divide r - 1, or
  # (36 | m, r = 3 mod 12, r/g = 5 or 7 mod 12).
  g = math.gcd(r, m); fs = factor(g) if g > 1 else []
  phi = 1; lam = 1
  for p in set(fs):
    e = fs.count(p); t = p ** (e - 1) * (p - 1); phi *= t
    lam = lam * t // math.gcd(lam, t)
  h = math.gcd(lam, m)
  bad = (math.gcd(g, 2 * phi) > 1 or (r - 1) % h != 0 or
         (m % 36 == 0 and r % 12 == 3 and (r // g) % 12 in (5, 7)))
  return not bad, g, lam, h

# ---- problem-specific check ----

print('2^280 mod 561 =', pow(2, 280, 561), ' 2^561 mod 544 =', pow(2, 561, 544))
assert pow(2, 280, 561) == 1 and 561 % 8 == 1 and pow(2, 561, 544) == 512
print('C027 OK')
