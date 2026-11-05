# Recursive interval LP bounds for Z-channel codes.
#
# W[m][(j1, j2)] = upper bound on |C cap weights j1..j2| for any length-m code.
# Levels m <= base come from exact/dual-bounded ILPs (runs/small_windows.json).
# Level m > base: an LP over layer sizes a_0..a_m with
#   - averaged clique rows,
#   - interval rows from all levels below (types t, m', j1, j2),
#   - monotone closure (a window is at most any window containing it),
# maximising sum_{w=j1}^{j2} a_w. Ends are not fixed (the simplicial swap
# can lower a window count), except when the window is everything.
#
import sys, json
from math import comb, floor
import numpy as np
import highspy

def close(Wm, m):
  for L in range(m + 1, 0, -1):
    for j1 in range(m + 1):
      j2 = j1 + L - 1
      if j2 > m: break
      v = Wm[(j1, j2)]
      if j1 > 0: v = min(v, Wm[(j1 - 1, j2)])
      if j2 < m: v = min(v, Wm[(j1, j2 + 1)])
      Wm[(j1, j2)] = v
  # A window can never exceed the sum of a split of it.
  #
  for L in range(2, m + 2):
    for j1 in range(m + 1):
      j2 = j1 + L - 1
      if j2 > m: break
      for s in range(j1, j2):
        Wm[(j1, j2)] = min(Wm[(j1, j2)], Wm[(j1, s)] + Wm[(s + 1, j2)])
  return Wm

def lp_window(n, W, j1, j2, fix_ends):
  h = highspy.Highs()
  h.setOptionValue('output_flag', False)
  inf = highspy.kHighsInf
  for w in range(n + 1):
    lo, hi = 0.0, float(comb(n, w))
    if fix_ends and w in (0, n): lo = hi = 1.0
    if fix_ends and w in (1, n - 1): lo = hi = 0.0
    h.addVar(lo, hi)
  cost = np.array([-1.0 if j1 <= w <= j2 else 0.0 for w in range(n + 1)])
  h.changeColsCost(n + 1, np.arange(n + 1, dtype=np.int32), cost)
  def row(coef, ub):
    idx = np.array(list(coef.keys()), dtype=np.int32)
    h.addRow(-inf, float(ub), len(idx), idx, np.array(list(coef.values()), dtype=float))
  for w in range(n + 1):
    if w + 1 <= n: row({ w: 1.0, w + 1: float(w + 1) }, comb(n, w))
    if w >= 1: row({ w: 1.0, w - 1: float(n - w + 1) }, comb(n, w))
  for m in W:
    if m >= n: continue
    for t in range(0, n - m + 1):
      for (k1, k2), b in W[m].items():
        coef = { t + j: float(comb(t + j, t) * comb(n - t - j, m - j)) for j in range(k1, k2 + 1) }
        row(coef, b * comb(n, t) * comb(n - t, m))
  if n in W:
    for (k1, k2), b in W[n].items():
      row({ w: 1.0 for w in range(k1, k2 + 1) }, b)
  h.run()
  return -h.getObjectiveValue()

if __name__ == '__main__':
  top = int(sys.argv[1])
  raw = json.load(open('runs/small_windows.json'))
  W = {}
  for k, v in raw.items():
    m, a, b = (int(x) for x in k.split(':'))
    W.setdefault(m, {})[(a, b)] = v
  for m in W:
    for (a, b) in list(W[m].keys()):
      W[m].setdefault((m - b, m - a), W[m][(a, b)])
    W[m] = close(W[m], m)
  base = max(W)
  # Exact n = 10 global windows (computed with the ends fixed are not
  # usable as general windows); keep only the full-window LP result.
  #
  for n in range(base + 1, top + 1):
    Wn = {}
    full = floor(lp_window(n, W, 0, n, True) + 1e-9)
    for j1 in range(n + 1):
      for j2 in range(j1, n + 1):
        v = lp_window(n, W, j1, j2, False)
        Wn[(j1, j2)] = floor(v + 1e-9)
    Wn[(0, n)] = min(Wn[(0, n)], full)
    # Exact window maxima from integer programs (zc_layers / zc_window1 for
    # this length; computed without fixing any word, so valid in general).
    #
    try:
      ex = json.load(open('runs/windows_n%d_known.json' % n))
      for k, v in ex.items():
        a, b = (int(x) for x in k.split('-'))
        Wn[(a, b)] = min(Wn[(a, b)], v)
        Wn[(n - b, n - a)] = min(Wn[(n - b, n - a)], v)
    except FileNotFoundError:
      pass
    W[n] = close(Wn, n)
    print('n=%d: full-code bound %d  (window 0..n LP without end fixing %d)' % (n, W[n][(0, n)], Wn[(0, n)]), flush=True)
  json.dump({ '%d:%d:%d' % (m, a, b): v for m in W for (a, b), v in W[m].items() }, open('runs/recursive_windows.json', 'w'))
