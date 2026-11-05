# Certificate for the n = 10 bound: solve the layer LP (no end fixing, so
# no symmetry argument is needed), take its dual, and re-verify the bound
# in exact rational arithmetic. Lists the window values the proof uses.
#
import sys, json
from fractions import Fraction as Fr
from math import comb
import numpy as np
import highspy
sys.path.insert(0, 'src')
from zc_recursive import close

n = int(sys.argv[1])
raw = json.load(open('runs/recursive_windows.json'))
W = {}
for k, v in raw.items():
  m, a, b = (int(x) for x in k.split(':'))
  W.setdefault(m, {})[(a, b)] = v

rows = []
for w in range(n + 1):
  if w + 1 <= n: rows.append(({ w: 1, w + 1: w + 1 }, comb(n, w), ('clique-up', w)))
  if w >= 1: rows.append(({ w: 1, w - 1: n - w + 1 }, comb(n, w), ('clique-down', w)))
ex = json.load(open('runs/windows_n%d_known.json' % n))
for k, b in ex.items():
  a, c = (int(x) for x in k.split('-'))
  rows.append(({ w: 1 for w in range(a, c + 1) }, b, ('global', n, a, c, b)))
for m in W:
  if m >= n: continue
  for t in range(0, n - m + 1):
    for (k1, k2), b in W[m].items():
      coef = { t + j: comb(t + j, t) * comb(n - t - j, m - j) for j in range(k1, k2 + 1) }
      rows.append((coef, b * comb(n, t) * comb(n - t, m), ('interval', m, t, k1, k2, b)))

h = highspy.Highs()
h.setOptionValue('output_flag', False)
inf = highspy.kHighsInf
for w in range(n + 1):
  h.addVar(0.0, float(comb(n, w)))
h.changeColsCost(n + 1, np.arange(n + 1, dtype=np.int32), -np.ones(n + 1))
for coef, ub, _ in rows:
  idx = np.array(list(coef.keys()), dtype=np.int32)
  h.addRow(-inf, float(ub), len(idx), idx, np.array([float(c) for c in coef.values()]))
h.run()
val = -h.getObjectiveValue()
y = h.getSolution().row_dual
# Exact check: with multipliers y_i >= 0 (rounded to rationals), every
# variable needs sum_i y_i coef_i[w] >= 1; then |C| = sum a_w <= sum_i y_i ub_i.
# Rows with dual ~0 are dropped; a small slack is repaired by scaling.
#
ys = [(Fr(-d).limit_denominator(10 ** 9), r) for d, r in zip(y, rows) if -d > 1e-12]
# Valid for any y >= 0: sum_w a_w <= sum_i y_i b_i + sum_w max(0, 1 - (A^T y)_w) * C(n, w).
#
cover = [sum(yi * Fr(r[0].get(w, 0)) for yi, r in ys) for w in range(n + 1)]
bound = sum(yi * Fr(r[1]) for yi, r in ys) + sum(max(Fr(0), 1 - c) * comb(n, w) for w, c in enumerate(cover))
print('LP value %.6f; exact certified bound %s = %.6f' % (val, bound, float(bound)))
print('rows used: %d' % len(ys))
used = sorted(set(('W', r[2][1], r[2][3], r[2][4], r[2][5]) if r[2][0] == 'interval' else r[2] for _, r in ys), key=str)
for u in used:
  print('  ', u)
json.dump([{ 'y': str(yi), 'row': r[2], 'ub': r[1] } for yi, r in ys], open('runs/certificate_n%d.json' % n, 'w'), indent=0)
