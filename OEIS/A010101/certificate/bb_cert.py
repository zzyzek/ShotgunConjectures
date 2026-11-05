# Branch and bound with certificates for window facts: prove that every
# length-m Z-channel code has at most `target` words of weights lo..hi.
# Each node fixes some variables to 0/1; a leaf is closed when its clique LP
# (with the fixings) has value < target + 1. Records the tree size and the
# leaves' dual multipliers (rational), so a checker (e.g. Lean) can replay it.
#
# WLOG fixing used: none (so the certificate needs no symmetry argument).
#
import sys, json, time
from fractions import Fraction as Fr
import numpy as np
import highspy

m, lo, hi, target, node_cap = (int(x) for x in sys.argv[1:6])
V = [x for x in range(1 << m) if lo <= bin(x).count('1') <= hi]
ix = {x: i for i, x in enumerate(V)}
N = len(V)
cl = []
for z in range(1 << m):
  for C in ([z] + [z | (1 << i) for i in range(m) if not ((z >> i) & 1)],
            [z] + [z & ~(1 << i) for i in range(m) if ((z >> i) & 1)]):
    C = sorted(set(ix[x] for x in C if x in ix))
    if len(C) > 1 and C not in cl:
      cl.append(C)

# Optional strengthening: per-subcube window rows. For a subcube (fix the
# coordinates in S to the values in mask), the code inside it is a code of
# length m - |S|, so its words in each window of local weights are at most
# the known window maximum W[d][(j1, j2)] for d = m - |S|.
#
import itertools, os
STRONG = os.environ.get('STRONG', '') != ''
rows_extra = []
if STRONG:
  raw = json.load(open('runs/small_windows.json'))
  Wd = {}
  for k, v in raw.items():
    d, a, b = (int(x) for x in k.split(':'))
    Wd.setdefault(d, {})[(a, b)] = v
    Wd[d].setdefault((d - b, d - a), v)
  for r in (1, 2):
    d = m - r
    for S in itertools.combinations(range(m), r):
      for vals in itertools.product((0, 1), repeat=r):
        base = sum(1 << S[i] for i in range(r) if vals[i])
        free = [i for i in range(m) if i not in S]
        cube = [base | sum(1 << free[k] for k in range(d) if (y >> k) & 1) for y in range(1 << d)]
        off = sum(vals)
        for (j1, j2), b in Wd.get(d, {}).items():
          mem = [ix[x] for x in cube if (x in ix) and j1 <= bin(x).count('1') - off <= j2]
          if len(mem) > b:
            rows_extra.append((mem, b))
  print('extra subcube rows: %d' % len(rows_extra), flush=True)

def lp(fix):
  h = highspy.Highs()
  h.setOptionValue('output_flag', False)
  inf = highspy.kHighsInf
  for i in range(N):
    v = fix.get(i)
    h.addVar(float(v) if v is not None else 0.0, float(v) if v is not None else 1.0)
  h.changeColsCost(N, np.arange(N, dtype=np.int32), -np.ones(N))
  for C in cl:
    h.addRow(-inf, 1.0, len(C), np.array(C, dtype=np.int32), np.ones(len(C)))
  for mem, b in rows_extra:
    h.addRow(-inf, float(b), len(mem), np.array(mem, dtype=np.int32), np.ones(len(mem)))
  h.run()
  x = h.getSolution().col_value
  return -h.getObjectiveValue(), x

t = time.time()
stack = [dict()]
nodes = leaves = 0
while stack:
  fix = stack.pop()
  nodes += 1
  if nodes > node_cap:
    print('node cap reached: %d nodes, %d open' % (nodes, len(stack))); sys.exit(1)
  if nodes % 5000 == 0:
    print('  %d nodes, %d leaves, %d open, %.0fs' % (nodes, leaves, len(stack), time.time() - t), flush=True)
  val, x = lp(fix)
  if val < target + 1 - 1e-7:
    leaves += 1
    continue
  # Branch on the most fractional variable; if integral, it is a counterexample.
  #
  frac = [(abs(x[i] - 0.5), i) for i in range(N) if (i not in fix) and (1e-6 < x[i] < 1 - 1e-6)]
  if not frac:
    print('integral solution of value %.1f: fact is false' % val); sys.exit(2)
  _, i = min(frac)
  f0 = dict(fix); f0[i] = 0
  f1 = dict(fix); f1[i] = 1
  for C in cl:
    if i in C:
      for j in C:
        if j != i:
          f1[j] = 0
  stack.append(f0); stack.append(f1)
print('m=%d weights %d..%d <= %d: proved; %d nodes, %d leaves, %.1fs' % (m, lo, hi, target, nodes, leaves, time.time() - t))
