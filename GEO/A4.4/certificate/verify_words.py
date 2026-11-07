# Exact (Fraction) verification of candidate periodic words from orbits.c: axis of G_w, start inside T,
# simulate k+1 bounces, require the face sequence w + w[0] with no edge hits and exact recurrence.
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from orbits import *
def check(word):
  w = tuple(int(c) for c in word)
  X = ([[F(int(r == s)) for s in range(3)] for r in range(3)], [F(0)]*3)
  for f in w: X = compose(X, R[f])
  M, t = X
  A = [[M[r][s] - (1 if r == s else 0) for s in range(3)] for r in range(3)]
  u = [F(x) for x in nullvec(A)]
  p = solve_axis(M, t, u)
  if p is None: return False
  for sign in (1, -1):
    uu = [sign*x for x in u]
    if dot(t, uu) <= 0: continue
    iv = inside_interval(p, uu)
    if iv is None: continue
    x = [pi + (iv[0]+iv[1])/2*ui for pi, ui in zip(p, uu)]
    if simulate(x, uu, w): return True
  return False
for path in sys.argv[1:]:
  ws = [l.strip() for l in open(path) if l.strip()]
  ok = sum(1 for s in ws if check(s))
  print(path, 'candidates', len(ws), 'exactly verified', ok, flush=True)
