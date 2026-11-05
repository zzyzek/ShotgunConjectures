# Upper bound for the Z-channel code size by weight layers.
#
# B(lo, hi) = exact maximum size of a code using only weights lo..hi
# (integer program on that subgraph). Then an LP over layer sizes a_w:
#   sum_{w in window} a_w <= B(window)            for every window solved
#   a_w + (w+1) a_{w+1} <= C(n, w)                (up-cliques, averaged)
#   a_w + (n-w+1) a_{w-1} <= C(n, w)              (down-cliques, averaged)
# with a_0 = a_n = 1 and a_1 = a_{n-1} = 0 (all-0 and all-1 words are in
# some optimal code, which empties weights 1 and n-1). The LP optimum is an
# upper bound on the code size.
#
import sys, time, json
from math import comb
import numpy as np
import highspy

def window_max(n, lo, hi, tlim, threads=1):
  V = [x for x in range(1 << n) if lo <= bin(x).count('1') <= hi]
  ix = {x: i for i, x in enumerate(V)}
  h = highspy.Highs()
  h.setOptionValue('output_flag', False)
  h.setOptionValue('time_limit', float(tlim))
  h.setOptionValue('threads', threads)
  inf = highspy.kHighsInf
  N = len(V)
  for _ in range(N):
    h.addVar(0.0, 1.0)
  h.changeColsCost(N, np.arange(N, dtype=np.int32), -np.ones(N))
  for z in range(1 << n):
    up = [z] + [z | (1 << i) for i in range(n) if not ((z >> i) & 1)]
    dn = [z] + [z & ~(1 << i) for i in range(n) if ((z >> i) & 1)]
    for C in (up, dn):
      C = [ix[x] for x in C if x in ix]
      if len(C) > 1:
        h.addRow(-inf, 1.0, len(C), np.array(C, dtype=np.int32), np.ones(len(C)))
  h.changeColsIntegrality(N, np.arange(N, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * N))
  t = time.time()
  h.run()
  obj = -h.getObjectiveValue()
  bd = -h.getInfo().mip_dual_bound
  return round(obj), bd, time.time() - t, h.modelStatusToString(h.getModelStatus())

def layer_lp(n, B):
  # Variables a_0..a_n.
  #
  h = highspy.Highs()
  h.setOptionValue('output_flag', False)
  inf = highspy.kHighsInf
  for w in range(n + 1):
    fixed = { 0: 1.0, n: 1.0, 1: 0.0, n - 1: 0.0 }
    lo = hi = fixed.get(w)
    h.addVar(lo if lo is not None else 0.0, hi if hi is not None else float(comb(n, w)))
  h.changeColsCost(n + 1, np.arange(n + 1, dtype=np.int32), -np.ones(n + 1))
  def row(coef, ub):
    idx = np.array(list(coef.keys()), dtype=np.int32)
    h.addRow(-inf, float(ub), len(idx), idx, np.array(list(coef.values()), dtype=float))
  for (lo, hi), b in B.items():
    row({ w: 1.0 for w in range(lo, hi + 1) }, b)
  for w in range(n + 1):
    if w + 1 <= n:
      row({ w: 1.0, w + 1: float(w + 1) }, comb(n, w))
    if w - 1 >= 0:
      row({ w: 1.0, w - 1: float(n - w + 1) }, comb(n, w))
  h.run()
  a = h.getSolution().col_value
  return -h.getObjectiveValue(), [round(x, 3) for x in a]

if __name__ == '__main__':
  n, k, tlim = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
  B = {}
  for width in range(1, k + 1):
    for lo in range(2, n - 1 - width + 1):
      hi = lo + width - 1
      if (n - hi, n - lo) in B:
        B[(lo, hi)] = B[(n - hi, n - lo)]
        continue
      v, bd, dt, st = window_max(n, lo, hi, tlim)
      ub = v if st == 'Optimal' else int(bd + 1e-6)
      B[(lo, hi)] = ub
      print('n=%d window %d..%d: max %d (bound %.2f, %s, %.1fs)' % (n, lo, hi, v, bd, st, dt), flush=True)
    val, a = layer_lp(n, B)
    print('n=%d windows up to width %d: LP bound %.3f  a=%s' % (n, width, val, a), flush=True)
  json.dump({ '%d-%d' % k2: v for k2, v in B.items() }, open('runs/windows_n%d.json' % n, 'w'))
