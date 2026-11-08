"""Given a covering assignment [(p, m, c, s)], x = 2^c (s in {0,-1}) or -2^c (s = 1) mod p,
compute the least odd CRT solution over the orbit x -> +-2^t x, t mod L."""
import sys, json
from sympy.ntheory.modular import crt
from math import prod
def orbit_min(assign, L):
  ps = [a[0] for a in assign]
  base = [ (pow(2, a[2], a[0]) if a[3] != 1 else (-pow(2, a[2], a[0])) % a[0]) for a in assign ]
  best = None
  for t in range(L):
    for sg in (1, -1):
      res = [ (sg * pow(2, t, p) * r) % p for p, r in zip(ps, base) ]
      x, M = crt(ps + [2], res + [1])
      x = int(x)
      if best is None or x < best[0]:
        best = (x, t, sg)
  return best, 2 * prod(ps)
if __name__ == "__main__":
  assign = json.loads(sys.argv[2]); L = int(sys.argv[1])
  (x, t, sg), M = orbit_min(assign, L)
  print("min x", x, "digits", len(str(x)), "t", t, "sign", sg, "modulus", M)
