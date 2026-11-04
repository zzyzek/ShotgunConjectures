# Independent re-check of NT-E29.1: own encoding, witness check at 3149,
# UNSAT at 3150 with solvers other than CaDiCaL/Glucose.
#
import sys, time, gzip
from pysat.solvers import Solver

def quads(lo, N):
  for x in range(lo, N + 1):
    for y in range(x + 1, N + 1):
      if (x * y) > N:
        break
      yield (x, y, x + y, x * y)

lo = 3
col = open('colouring_3_3149.txt').read().strip()
c = { lo + i: int(ch) for i, ch in enumerate(col) }
assert (len(c) == 3149 - lo + 1)
bad = [ q for q in quads(lo, 3149) if len({ c[v] for v in q }) == 1 ]
print('witness [3,3149]: %d monochromatic quadruples' % len(bad))

cls = []
for q in quads(lo, 3150):
  cls.append(list(q)); cls.append([-v for v in q])
mine = set(tuple(sorted(x)) for x in cls)
theirs = set()
for l in gzip.open('unsat_3_3150.cnf.gz', 'rt'):
  if l[0] in 'pc':
    continue
  t = tuple(sorted(int(v) for v in l.split()[:-1]))
  if t:
    theirs.add(t)
print('clauses mine %d theirs %d identical %s' % (len(mine), len(theirs), mine == theirs))

for name in ('lingeling', 'minisat22', 'maplechrono'):
  t0 = time.time()
  with Solver(name=name, bootstrap_with=cls) as s:
    r = s.solve()
  print('%s: N=3150 %s (%.1fs)' % (name, 'SAT' if r else 'UNSAT', time.time() - t0), flush=True)
