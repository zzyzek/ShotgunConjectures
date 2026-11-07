# Periodic billiard orbits in the regular tetrahedron, exact rationals.
# For each cyclic face word w (first face 0, no immediate repeats incl. wrap-around) of even length k,
# G = s_{w1} ... s_{wk} (reflections in the faces of the original tetrahedron).  A periodic orbit with
# word w lies on the screw axis of G: direction u = fixed vector of the linear part, axis point p.
# The orbit is accepted if the billiard started on the axis inside T hits exactly the faces w (no edge
# hits) and returns to the start point with the start direction.
import sys
from fractions import Fraction as F
sys.path.insert(0, __import__('os').path.dirname(__file__))
from words import V, R, compose, words
def nullvec(A):
  # nonzero rational vector in the kernel of 3x3 A (assumed rank 2)
  for (i, j) in ((0, 1), (0, 2), (1, 2)):
    a, b = A[i], A[j]
    c = [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
    if any(c): return c
  return None
def dot(a, b): return sum(x*y for x, y in zip(a, b))
def solve_axis(M, t, u):
  # find p with (M - I) p = -(t - (t.u/u.u) u), p.u = 0
  tp = [ti - dot(t, u)/dot(u, u)*ui for ti, ui in zip(t, u)]
  A = [[M[r][s] - (1 if r == s else 0) for s in range(3)] + [-tp[r]] for r in range(3)]
  A.append(list(u) + [F(0)])
  # least squares exact: solve normal equations of the 4x3 system
  N = [[sum(A[r][i]*A[r][j] for r in range(4)) for j in range(3)] for i in range(3)]
  b = [sum(A[r][i]*A[r][3] for r in range(4)) for i in range(3)]
  # Gaussian elimination
  m = [N[i] + [b[i]] for i in range(3)]
  for c in range(3):
    piv = next(r for r in range(c, 3) if m[r][c] != 0)
    m[c], m[piv] = m[piv], m[c]
    for r in range(3):
      if r != c and m[r][c] != 0:
        f = m[r][c]/m[c][c]
        m[r] = [x - f*y for x, y in zip(m[r], m[c])]
  p = [m[i][3]/m[i][i] for i in range(3)]
  # check exactness
  for r in range(4):
    if sum(A[r][i]*p[i] for i in range(3)) != A[r][3]: return None
  return p
NRM = [[-c for c in v] for v in V]
def inside_interval(p, u):
  lo, hi = None, None
  for n in NRM:
    a, b = dot(n, u), 1 - dot(n, p)   # n.(p + s u) <= 1  <=>  s a <= b
    if a == 0:
      if b <= 0: return None
    elif a > 0:
      hi = b/a if hi is None else min(hi, b/a)
    else:
      lo = b/a if lo is None else max(lo, b/a)
  if lo is None or hi is None or lo >= hi: return None
  return lo, hi
def simulate(x, u, w):
  # Bounce k+1 times along w + w[0]; periodic iff the state after bounce 1 recurs after bounce k+1.
  w = list(w) + [w[0]]
  states = []
  for f in w:
    best, hit = None, []
    for i, n in enumerate(NRM):
      a = dot(n, u)
      if a > 0:
        s = (1 - dot(n, x))/a
        if best is None or s < best: best, hit = s, [i]
        elif s == best: hit.append(i)
    if len(hit) != 1 or hit[0] != f: return False
    x = [xi + best*ui for xi, ui in zip(x, u)]
    n = NRM[f]; c = 2*dot(n, u)/3
    u = [ui - c*ni for ui, ni in zip(u, n)]
    states.append((x, u))
  return states[0] == states[-1]
if __name__ == '__main__':
  kmax = int(sys.argv[1])
  for k in range(2, kmax+1, 2):
    found = []
    for w in words(k):
      if w[0] != 0: continue
      X = ([[F(int(r == s)) for s in range(3)] for r in range(3)], [F(0)]*3)
      for f in w:
        X = compose(X, R[f])
      M, t = X
      A = [[M[r][s] - (1 if r == s else 0) for s in range(3)] for r in range(3)]
      u = nullvec(A)
      if u is None: continue
      u = [F(x) for x in u]
      p = solve_axis(M, t, u)
      if p is None: continue
      for sign in (1, -1):
        uu = [sign*x for x in u]
        # direction must be carried forward by G: t . u > 0 along the axis
        if dot(t, uu) <= 0: continue
        iv = inside_interval(p, uu)
        if iv is None: continue
        s = (iv[0] + iv[1])/2
        x = [pi + s*ui for pi, ui in zip(p, uu)]
        if simulate(x, uu, w):
          found.append(''.join(map(str, w)))
    # primitive words only, up to rotation
    prim = set()
    for s in found:
      if any(k % d == 0 and s == s[:d]*(k//d) for d in range(1, k)): continue
      rots = [s[i:]+s[:i] for i in range(k)]
      prim.add(min(rots))
    print('k', k, 'periodic words (first face 0, all rotations)', len(found), 'primitive up to rotation', len(prim), sorted(prim)[:6], flush=True)
