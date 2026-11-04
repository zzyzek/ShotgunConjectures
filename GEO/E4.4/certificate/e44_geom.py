# GEO-E4.4: cross-check the SAT encoding against exact geometry on random
# integer point sets in general position: (1) the orientation assignment
# satisfies the signotope clauses, (2) the clause-level "meets" predicate
# equals an exact segment/open-triangle test (clip the segment parameter
# against three strict half-planes with rational arithmetic), (3) a Birch
# partition exists (as UNSAT predicts).
#
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
sys.argv = ['x', '8']
import e44_sat as E
def orient(P, a, b, c):
  (x1, y1), (x2, y2), (x3, y3) = P[a], P[b], P[c]
  return (x2-x1)*(y3-y1) - (y2-y1)*(x3-x1)
def meets_exact(P, p, q, tri):
  a, b, c = tri
  if orient(P, a, b, c) < 0: b, c = c, b
  lo, hi = Fraction(0), Fraction(1)
  for u, v in ((a, b), (b, c), (c, a)):
    # g(t) = orient(u, v, p + t (q - p)) > 0, affine in t
    g0 = orient(P, u, v, p); g1 = orient(P, u, v, q)
    # g(t) = g0 + t (g1 - g0)
    d = g1 - g0
    if d == 0:
      if g0 <= 0: return False
    elif d > 0: lo = max(lo, Fraction(-g0, d))
    else: hi = min(hi, Fraction(-g0, d))
  return lo < hi
rnd = random.Random(7); tested = 0; mism = 0; nobirch = 0
while tested < 2000:
  P = sorted({(rnd.randint(0, 60), rnd.randint(0, 60)) for _ in range(8)})
  if len(P) < 8 or len({x for x, _ in P}) < 8: continue
  if any(orient(P, *t) == 0 for t in itertools.combinations(range(8), 3)): continue
  asg = {}
  for t, v in E.var.items(): asg[v] = orient(P, *t) > 0
  lit = lambda l: asg[l] if l > 0 else not asg[-l]
  assert all(any(lit(l) for l in c) for c in E.cls[:E.signotope_clauses])
  found = False
  for seg in itertools.combinations(range(8), 2):
    rest = [x for x in range(8) if x not in seg]
    for t1 in itertools.combinations(rest, 3):
      t2 = tuple(x for x in rest if x not in t1)
      r = []
      for t in (t1, t2):
        enc = any(all(lit(l) for l in term) for term in E.terms(seg[0], seg[1], t))
        ex = meets_exact(P, seg[0], seg[1], t)
        if enc != ex: mism += 1
        r.append(ex)
      if all(r): found = True
  nobirch += (not found); tested += 1
print("random sets", tested, "predicate mismatches", mism, "sets without Birch partition", nobirch)
