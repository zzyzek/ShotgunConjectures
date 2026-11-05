# Iterate window bounds at length n to a fixpoint: each window's LP bound
# (interval rows from smaller lengths + current length-n window rows) is
# floored and fed back. Valid at every step: each value is an upper bound.
#
import sys, json
from math import floor
sys.path.insert(0, 'src')
from zc_recursive import lp_window, close

n = int(sys.argv[1])
raw = json.load(open('runs/small_windows.json'))
W = {}
for k, v in raw.items():
  m, a, b = (int(x) for x in k.split(':'))
  W.setdefault(m, {})[(a, b)] = v
for m in W:
  for (a, b) in list(W[m]):
    W[m].setdefault((m - b, m - a), W[m][(a, b)])
  W[m] = close(W[m], m)
ex = json.load(open('runs/windows_n%d_known.json' % n))
Wn = { (a, b): 10 ** 6 for a in range(n + 1) for b in range(a, n + 1) }
for k, v in ex.items():
  a, b = (int(x) for x in k.split('-'))
  Wn[(a, b)] = min(Wn[(a, b)], v); Wn[(n - b, n - a)] = min(Wn[(n - b, n - a)], v)
W[n] = Wn
for it in range(20):
  changed = 0
  for (a, b) in sorted(Wn, key=lambda t: t[1] - t[0]):
    v = floor(lp_window(n, W, a, b, False) + 1e-9)
    if v < Wn[(a, b)]:
      Wn[(a, b)] = v; Wn[(n - b, n - a)] = min(Wn[(n - b, n - a)], v); changed += 1
  W[n] = close(Wn, n)
  full = lp_window(n, W, 0, n, False)
  print('iteration %d: %d windows tightened; full LP %.4f; B(3,5)=%d B(2,5)=%d' % (it, changed, full, Wn[(3, 5)], Wn[(2, 5)]), flush=True)
  if not changed:
    break
json.dump({ '%d-%d' % k: v for k, v in Wn.items() }, open('runs/fixpoint_n%d.json' % n, 'w'))
