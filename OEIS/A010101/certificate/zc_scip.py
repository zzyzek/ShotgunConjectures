# Independent check of window facts with SCIP (no shared code with HiGHS):
# maximum Z-channel code of length m using weights lo..hi, pairwise
# conflict constraints only (no clique strengthening).
#
import sys, time
from pyscipopt import Model, quicksum
m, lo, hi = (int(x) for x in sys.argv[1:4])
V = [x for x in range(1 << m) if lo <= bin(x).count('1') <= hi]
M = Model()
M.hideOutput()
M.setParam('limits/time', float(sys.argv[4]) if len(sys.argv) > 4 else 3600.0)
M.setParam('parallel/maxnthreads', 1)
X = { x: M.addVar(vtype='B') for x in V }
if len(sys.argv) > 5 and sys.argv[5] == 'clique':
  # Cliques: z with its one-up (or one-down) neighbours; they cover every conflict.
  #
  for z in range(1 << m):
    for C in ([z] + [z | (1 << i) for i in range(m) if not ((z >> i) & 1)],
              [z] + [z & ~(1 << i) for i in range(m) if ((z >> i) & 1)]):
      C = [x for x in C if x in X]
      if len(C) > 1:
        M.addCons(quicksum(X[x] for x in C) <= 1)
else:
  for x in V:
    for y in V:
      if x < y and max(bin(x & ~y).count('1'), bin(y & ~x).count('1')) <= 1:
        M.addCons(X[x] + X[y] <= 1)
M.setObjective(quicksum(X.values()), 'maximize')
t = time.time()
M.optimize()
print('SCIP m=%d weights %d..%d: status %s, max %s, dual bound %.3f, %.1fs' % (m, lo, hi, M.getStatus(), round(M.getObjVal()), M.getDualbound(), time.time() - t), flush=True)
