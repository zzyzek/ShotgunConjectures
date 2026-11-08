"""Certificate check that an odd x is not of the form +-p^a +- 2^b (p prime, a >= 0, b >= 0).

1. Covering: S = primes, L = common multiple of ord_p(2). For every b mod L, the primes in S
   dividing x - 2^b (side '-') and x + 2^b (side '+') are listed; every class must be hit.
2. A class hit by >= 2 distinct primes: |x -+ 2^b| has two prime factors, not a prime power.
3. A class hit by exactly one prime p: exclude x - 2^b = e p^a (e = +-1) and x + 2^b = p^a for
   b >= B0 using auxiliary primes q with ord_q(2) | L (then 2^b mod q is fixed on the class) and
   the 2-adic constraint mod 2^K (valid for b >= K): the admissible exponents a, intersected
   over all moduli, must be empty.
4. b < B0 = max(K, bit length of x + 1): checked directly (|x -+ 2^b| is not +-1 and is not a
   power of a single prime: it has a prime factor in S and is not a pure power of it).
Usage: python3 verify_x.py x L p1,p2,...  [qmax]"""
import sys
from math import gcd, lcm
from sympy import primerange, n_order, isprime

def adm(p, target, q):
  # set of a mod ord_q(p) with p^a = target (mod q)
  o = n_order(p, q); t = target % q; s = set(); v = 1
  for a in range(o):
    if v == t: s.add(a)
    v = (v * p) % q
  return o, s

def intersect(cur, new):
  (m1, s1), (m2, s2) = cur, new
  m = lcm(m1, m2)
  if m > 10**7:
    return None
  out = set()
  for a in range(m):
    if (a % m1) in s1 and (a % m2) in s2: out.add(a)
  return (m, out)

def main():
  x = int(sys.argv[1]); L = int(sys.argv[2]); S = [int(t) for t in sys.argv[3].split(',')]
  qmax = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
  assert x % 2 == 1 and x > 0
  for p in S: assert isprime(p) and L % n_order(2, p) == 0
  hit = {}
  for side in (-1, 1):
    for b in range(L):
      hp = [p for p in S if (x + side * pow(2, b, p)) % p == 0]
      assert hp, ("uncovered", side, b)
      hit[(side, b)] = hp
  single = [(side, b, hp[0]) for (side, b), hp in hit.items() if len(hp) == 1]
  print("covering OK; classes", 2 * L, "single-prime classes", len(single))
  aux = [q for q in primerange(3, qmax) if L % n_order(2, q) == 0]
  K = 20
  B0 = max(K, (x + 1).bit_length() + 1)
  bad = []
  for (side, b0, p) in single:
    # Equations: side -1: x - 2^b = e p^a, e = +-1 ; side +1: x + 2^b = p^a.
    for e in ((1, -1) if side == -1 else (1,)):
      # 2-adic: for b >= K, e p^a = x (mod 2^K)
      M2 = 1 << K
      o2 = n_order(p, M2); s2 = set(); v = 1
      for a in range(o2):
        if (e * v - x) % M2 == 0: s2.add(a)
        v = (v * p) % M2
      cur = (o2, s2)
      for q in aux:
        if not cur[1]: break
        if q == p: continue
        y = (x + side * pow(2, b0, q)) % q
        t = (e * y) % q
        nw = adm(p, t, q)
        r = intersect(cur, nw)
        if r is not None: cur = r
      if cur[1]:
        bad.append((side, b0, p, e, cur[0], len(cur[1])))
  print("single-prime classes not excluded:", len(bad), bad[:10])
  # small b, direct
  for b in range(B0 + L):
    for side in (-1, 1):
      v = abs(x + side * (1 << b))
      assert v > 1
      hp = [p for p in S if v % p == 0]
      assert hp
      for p in hp:
        w = v
        while w % p == 0: w //= p
        assert w != 1, ("prime power", b, side, p)
  print("direct check of b <", B0 + L, "OK")
  print("RESULT", "PROVED" if not bad else "INCOMPLETE")

if __name__ == "__main__":
  main()
