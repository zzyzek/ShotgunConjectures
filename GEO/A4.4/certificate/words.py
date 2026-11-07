# Regular tetrahedron billiard: for each face word w (no immediate repeats, length n), compose the face
# reflections exactly (Fractions) and classify the isometry R_w.  Odd n: periodic orbits need R_w to be
# a glide reflection (linear part a reflection, glide vector g != 0); even n: translation (linear part I)
# or screw motion along an axis.  Candidates are then tested by simulating the billiard (exact rationals).
import itertools, sys
from fractions import Fraction as F
V = [(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
# face i = plane through the vertices other than V[i]; outward normal = -V[i]; plane: -V[i].x = 1
def refl(i):
  n = [-c for c in V[i]]; c = 1; nn = 3
  # x -> x - 2 (n.x - c)/nn n
  M = [[F(int(r == s)) - F(2*n[r]*n[s], nn) for s in range(3)] for r in range(3)]
  t = [F(2*c*n[r], nn) for r in range(3)]
  return (M, t)
R = [refl(i) for i in range(4)]
def compose(A, B):
  # A after B
  (MA, tA), (MB, tB) = A, B
  M = [[sum(MA[r][k]*MB[k][s] for k in range(3)) for s in range(3)] for r in range(3)]
  t = [sum(MA[r][k]*tB[k] for k in range(3)) + tA[r] for r in range(3)]
  return (M, t)
def word_iso(w):
  X = ([[F(int(r == s)) for s in range(3)] for r in range(3)], [F(0)]*3)
  for f in w:
    X = compose(R[f], X)
  return X
def det3(M):
  return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
          + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
def trace(M): return M[0][0]+M[1][1]+M[2][2]
def words(n):
  for first in range(4):
    def rec(w):
      if len(w) == n:
        if w[-1] != w[0]: yield tuple(w)
        return
      for f in range(4):
        if f != w[-1]:
          w.append(f); yield from rec(w); w.pop()
    yield from rec([first])
if __name__ == '__main__':
  n = int(sys.argv[1])
  cnt = {}
  for w in words(n):
    M, t = word_iso(w)
    d = det3(M); tr = trace(M)
    key = (int(d), str(tr))
    cnt[key] = cnt.get(key, 0) + 1
  print(n, sorted(cnt.items()))
