# Birch (CFG E4): does every 8-point set in general position split into two
# triangles and a segment meeting the interiors of both triangles?
# Encode all simple x-sorted pseudoline arrangements (signotopes) on n
# points: variables chi(i,j,k), i<j<k, true = counterclockwise; for each
# i<j<k<l the sequence chi(jkl), chi(ikl), chi(ijl), chi(ijk) changes
# sign at most once.  Every uniform rank-3 oriented matroid with n <= 8
# is realizable (Goodman-Pollack), so UNSAT = theorem for general position
# and a model = a realizable counterexample order type.
#
import sys, itertools
from pysat.solvers import Cadical153
from pysat.formula import IDPool
n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
pool = IDPool()
def chi(a, b, c):
  t = [a, b, c]
  s = sorted(t)
  inv = sum(1 for x in range(3) for y in range(x + 1, 3) if t[x] > t[y])
  v = pool.id(("c",) + tuple(s))
  return v if inv % 2 == 0 else -v
C = []
for i, j, k, l in itertools.combinations(range(n), 4):
  seq = [chi(j, k, l), chi(i, k, l), chi(i, j, l), chi(i, j, k)]

  # At most one sign change: forbid patterns +-+ and -+- on any
  # three positions in order.
  #
  for x, y, z in itertools.combinations(range(4), 3):
    C.append([-seq[x], seq[y], -seq[z]])
    C.append([seq[x], -seq[y], seq[z]])
def AND(lits):
  v = pool.id(("and",) + tuple(lits))
  for l in lits:
    C.append([-v, l])
  C.append([v] + [-l for l in lits])
  return v
def OR(lits):
  v = pool.id(("or",) + tuple(lits))
  for l in lits:
    C.append([v, -l])
  C.append([-v] + list(lits))
  return v
def XOR(a, b):
  v = pool.id(("xor", a, b))
  C.extend([[-v, a, b], [-v, -a, -b], [v, -a, b], [v, a, -b]])
  return v
def inside(p, a, b, c):
  o = chi(a, b, c)
  return OR([AND([chi(a, b, p), chi(b, c, p), chi(c, a, p), o]),
             AND([-chi(a, b, p), -chi(b, c, p), -chi(c, a, p), -o])])
def cross(p, q, u, v):
  return AND([XOR(chi(p, q, u), chi(p, q, v)), XOR(chi(u, v, p), chi(u, v, q))])
def hit(p, q, T):
  a, b, c = T
  return OR([inside(p, a, b, c), inside(q, a, b, c),
             cross(p, q, a, b), cross(p, q, b, c), cross(p, q, c, a)])
parts = 0
for s in itertools.combinations(range(n), 2):
  rest = [i for i in range(n) if i not in s]
  for A in itertools.combinations(rest, 3):
    if rest[0] not in A:
      continue
    B = tuple(i for i in rest if i not in A)
    C.append([-hit(s[0], s[1], A), -hit(s[0], s[1], B)])
    parts += 1
with Cadical153(bootstrap_with=C) as S:
  r = S.solve()
  print("n=%d partitions=%d vars=%d clauses=%d -> %s" % (n, parts, pool.top, len(C), "SAT (counterexample order type)" if r else "UNSAT (property holds for all simple order types)"))
  if r:
    m = set(S.get_model())
    print({k: (pool.id(("c",) + k) in m) for k in itertools.combinations(range(n), 3)})
