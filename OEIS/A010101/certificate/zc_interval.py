# Layer LP for the Z-channel code size strengthened by interval constraints.
#
# An interval [T, Z] of the Boolean lattice (T subset of Z, |T| = t,
# |Z| = t + m) is a copy of the m-cube, and conflicts inside it are the
# Z-channel conflicts of length m (weights shifted by t). So a code meets
# it in a length-m Z-channel code, and its part in global weights
# t+j1..t+j2 is at most W_m(j1, j2), the exact window maximum for length m.
# Summing over all intervals of a given type: a word of weight w lies in
# C(w, t) * C(n - w, t + m - w) of them, and there are C(n, t) * C(n - t, m)
# intervals, so
#   sum_{w = t+j1}^{t+j2} a_w C(w, t) C(n-w, t+m-w) <= W_m(j1, j2) C(n, t) C(n-t, m).
# Plus the global windows of zc_layers and the averaged clique rows.
# The LP optimum bounds the code size.
#
import sys, json, os
from math import comb
import numpy as np
import highspy
sys.path.insert(0, os.path.dirname(__file__))
from zc_layers import window_max

def small_windows(mmax, tlim, cache='runs/small_windows.json'):
  W = json.load(open(cache)) if os.path.exists(cache) else {}
  for m in range(1, mmax + 1):
    for j1 in range(m + 1):
      for j2 in range(j1, m + 1):
        key = '%d:%d:%d' % (m, j1, j2)
        if key in W:
          continue
        mirror = '%d:%d:%d' % (m, m - j2, m - j1)
        if mirror in W:
          W[key] = W[mirror]
          continue
        v, bd, dt, st = window_max(m, j1, j2, tlim)
        W[key] = v if st == 'Optimal' else int(bd + 1e-6)
        print('m=%d window %d..%d: %d (%s, %.1fs)' % (m, j1, j2, W[key], st, dt), flush=True)
        json.dump(W, open(cache, 'w'))
  return W

def lp(n, W, B, mmax, fix_ends=True):
  h = highspy.Highs()
  h.setOptionValue('output_flag', False)
  inf = highspy.kHighsInf
  for w in range(n + 1):
    lo, hi = 0.0, float(comb(n, w))
    if fix_ends and w in (0, n): lo = hi = 1.0
    if fix_ends and w in (1, n - 1): lo = hi = 0.0
    h.addVar(lo, hi)
  h.changeColsCost(n + 1, np.arange(n + 1, dtype=np.int32), -np.ones(n + 1))
  rows = 0
  def row(coef, ub):
    idx = np.array(list(coef.keys()), dtype=np.int32)
    h.addRow(-inf, float(ub), len(idx), idx, np.array(list(coef.values()), dtype=float))
  for (lo, hi), b in B.items():
    row({ w: 1.0 for w in range(lo, hi + 1) }, b); rows += 1
  for w in range(n + 1):
    if w + 1 <= n: row({ w: 1.0, w + 1: float(w + 1) }, comb(n, w)); rows += 1
    if w >= 1: row({ w: 1.0, w - 1: float(n - w + 1) }, comb(n, w)); rows += 1
  for m in range(1, mmax + 1):
    for t in range(0, n - m + 1):
      for j1 in range(m + 1):
        for j2 in range(j1, m + 1):
          coef = { t + j: float(comb(t + j, t) * comb(n - t - j, m - j)) for j in range(j1, j2 + 1) }
          row(coef, W['%d:%d:%d' % (m, j1, j2)] * comb(n, t) * comb(n - t, m)); rows += 1
  h.run()
  return -h.getObjectiveValue(), [round(x, 3) for x in h.getSolution().col_value], rows

if __name__ == '__main__':
  n, mmax, tlim = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
  W = small_windows(mmax, tlim)
  B = {}
  if os.path.exists('runs/windows_n%d_known.json' % n):
    B = { tuple(int(x) for x in k.split('-')): v for k, v in json.load(open('runs/windows_n%d_known.json' % n)).items() }
  for mm in range(1, mmax + 1):
    val, a, rows = lp(n, W, B, mm)
    print('n=%d intervals up to dim %d (+%d global windows): LP %.3f  a=%s' % (n, mm, len(B), val, a), flush=True)
