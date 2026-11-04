# GEO-E4.4 independent recheck (second reader; written without reading the
# scan's om.py).  Points 0..7 sorted by x-coordinate; variable X(i,j,k),
# i<j<k, is true when (i,j,k) is counterclockwise.  Every point set in
# general position gives a signotope: for i<j<k<l the sequence
# X(ijk), X(ijl), X(ikl), X(jkl) changes value at most once.
# For each of the 280 partitions {segment, triangle, triangle} we forbid
# "segment meets the open triangle" for both triangles.  In general position
# the segment pq meets the open triangle abc iff p or q is strictly inside,
# or pq properly crosses an edge.  UNSAT means every set of 8 points in
# general position has a Birch partition.
#
import sys, itertools, random
from fractions import Fraction
from pysat.solvers import Cadical153
from pysat.formula import CNF
N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
var = {}
for t in itertools.combinations(range(N), 3): var[t] = len(var) + 1
nv = len(var)
def o(a, b, c):
  # literal for "orient(a,b,c) > 0"
  t = (a, b, c); s = tuple(sorted(t))
  perm = [s.index(x) for x in t]
  inv = sum(1 for i in range(3) for j in range(i+1, 3) if perm[i] > perm[j])
  return var[s] if inv % 2 == 0 else -var[s]
cls = []
for i, j, k, l in itertools.combinations(range(N), 4):
  seq = [var[(i,j,k)], var[(i,j,l)], var[(i,k,l)], var[(j,k,l)]]
  for a, b, c in itertools.combinations(range(4), 3):
    cls.append([-seq[a], seq[b], -seq[c]])
    cls.append([seq[a], -seq[b], seq[c]])
signotope_clauses = len(cls)
def terms(p, q, tri):
  a, b, c = tri
  out = []
  for x in (p, q):
    l1, l2, l3 = o(a, b, x), o(b, c, x), o(c, a, x)
    out.append([l1, l2, l3]); out.append([-l1, -l2, -l3])
  for u, v in ((a, b), (b, c), (c, a)):
    A, B = o(p, q, u), o(p, q, v)
    C, D = o(u, v, p), o(u, v, q)
    for sA in (1, -1):
      for sC in (1, -1):
        out.append([sA*A, -sA*B, sC*C, -sC*D])
  return out
M = {}
def meet(seg, tri, mode):
  key = (seg, tri)
  if key not in M:
    global nv
    nv += 1; M[key] = nv
    ts = terms(seg[0], seg[1], tri)
    if mode == 'endpoint': ts = ts[:4]
    for t in ts: cls.append([-x for x in t] + [nv])
  return M[key]
def build(mode):
  parts = 0
  for seg in itertools.combinations(range(N), 2):
    rest = [x for x in range(N) if x not in seg]
    for t1 in itertools.combinations(rest, 3):
      t2 = tuple(x for x in rest if x not in t1)
      if t1 > t2: continue
      cls.append([-meet(seg, t1, mode), -meet(seg, t2, mode)]); parts += 1
  return parts
if __name__ == '__main__':
  mode = sys.argv[2] if len(sys.argv) > 2 else 'full'
  if mode == 'count':
    s = Cadical153(bootstrap_with=cls); c = 0
    for m in s.enum_models(): c += 1
    print("signotopes on", N, "points:", c); sys.exit()
  parts = build(mode)
  print("N", N, "mode", mode, "partitions", parts, "vars", nv, "clauses", len(cls))
  s = Cadical153(bootstrap_with=cls, with_proof=True)
  r = s.solve(); print("SAT" if r else "UNSAT")
  if not r:
    CNF(from_clauses=cls).to_file('e44.cnf')
    with open('e44.drat', 'w') as f: f.write('\n'.join(s.get_proof()) + '\n')
    print("proof lines", len(s.get_proof()))
