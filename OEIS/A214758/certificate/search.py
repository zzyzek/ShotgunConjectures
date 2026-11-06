"""A214758 (Coman): a Carmichael number C1 = (C2 + C3)/2 with C2, C3
Carmichael only if C2 divides both C1 and C3.  Lists all triples
C2 < C1 < C3 < bound with 2 C1 = C2 + C3 and reports those where C2 does not
divide C1 or C3 (Carmichael numbers by Korselt's criterion, sympy factorint).
Usage: python3 search.py [bound]
"""
import sys
import sympy as sp
bound = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 6


def korselt(n):
  f = sp.factorint(n)
  return len(f) >= 2 and all(e == 1 for e in f.values()) and all((n - 1) % (p - 1) == 0 for p in f)


C = [n for n in range(3, bound, 2) if not sp.isprime(n) and korselt(n)]
S = set(C)
tot = bad = 0
for i, c2 in enumerate(C):
  for c1 in C[i + 1:]:
    c3 = 2 * c1 - c2
    if c3 >= bound:
      break
    if c3 in S:
      tot += 1
      if c1 % c2 or c3 % c2:
        bad += 1
        if bad <= 10:
          print("counterexample", c1, "= (", c2, "+", c3, ")/2", sp.factorint(c2), sp.factorint(c1), sp.factorint(c3))
print(len(C), "Carmichael numbers below", bound, ";", tot, "triples,", bad, "counterexamples")
