# Random simple-ish squared rectangles via Brooks-Smith-Stone-Tutte.
# Graph: convex hull triangulation of random points on a sphere, then random
# edge deletions keeping 3-connectivity.  Faces are tracked with union-find
# so the embedding survives deletions.  Kirchhoff (exact rationals) gives
# y = vertex potentials, x = face potentials; each edge is a placed square.
# Output: list of (size, x, y) with integer coordinates, W, H.
#
import random, itertools
from fractions import Fraction
import numpy as np
from scipy.spatial import ConvexHull

def solve_exact(A, b):
  n = len(A)
  M = [[Fraction(v) for v in row] + [Fraction(bb)] for row, bb in zip(A, b)]
  for c in range(n):
    p = next(r for r in range(c, n) if M[r][c] != 0)
    M[c], M[p] = M[p], M[c]
    for r in range(n):
      if r != c and M[r][c] != 0:
        f = M[r][c] / M[c][c]
        M[r] = [a - f * bv for a, bv in zip(M[r], M[c])]
  return [M[i][n] / M[i][i] for i in range(n)]

def connected(nv, E, removed):
  adj = {v: [] for v in range(nv) if v not in removed}
  for u, v in E:
    if u in adj and v in adj:
      adj[u].append(v); adj[v].append(u)
  if not adj:
    return True
  st = [next(iter(adj))]; seen = set(st)
  while st:
    for w in adj[st.pop()]:
      if w not in seen:
        seen.add(w); st.append(w)
  return len(seen) == len(adj)

def three_connected(nv, E):
  if nv < 4:
    return False
  return all(connected(nv, E, {a, b}) for a, b in itertools.combinations(range(nv), 2))

def random_graph(rnd, nv, ndel):
  P = np.array([[rnd.gauss(0, 1) for _ in range(3)] for _ in range(nv)])
  hull = ConvexHull(P)
  cen = P.mean(axis=0)
  faces = []
  for s in hull.simplices:
    a, b, c = (int(v) for v in s)
    if np.dot(np.cross(P[b] - P[a], P[c] - P[a]), P[a] - cen) < 0:
      b, c = c, b
    faces.append((a, b, c))
  if len({v for f in faces for v in f}) != nv:
    return None
  left = {}
  for fi, (a, b, c) in enumerate(faces):
    for u, v in ((a, b), (b, c), (c, a)):
      left[(u, v)] = fi
  E = {tuple(sorted(k)) for k in left}
  parent = list(range(len(faces)))
  def find(x):
    while parent[x] != x:
      parent[x] = parent[parent[x]]; x = parent[x]
    return x
  for _ in range(ndel):
    e = rnd.choice(sorted(E))
    E2 = E - {e}
    if three_connected(nv, E2):
      E = E2
      parent[find(left[e])] = find(left[(e[1], e[0])])
  return nv, sorted(E), left, find

def squared(nv, E, left, find, battery):
  s, t = battery
  idx = [v for v in range(nv) if v != t]
  pos = {v: i for i, v in enumerate(idx)}
  A = [[0] * (nv - 1) for _ in range(nv - 1)]
  for u, v in E:
    if {u, v} == {s, t}:
      continue
    for a, b in ((u, v), (v, u)):
      if a != t:
        A[pos[a]][pos[a]] += 1
        if b != t:
          A[pos[a]][pos[b]] -= 1
  rhs = [0] * (nv - 1); rhs[pos[s]] = 1
  x = solve_exact(A, rhs)
  pot = {v: (Fraction(0) if v == t else x[pos[v]]) for v in range(nv)}
  W = Fraction(1); H = pot[s]

  # Face potentials: crossing directed edge u->v (current u->v) from its
  # left face to its right face adds the current.  The battery edge is
  # not crossed; its two faces become the sides x=0 and x=W.
  #
  sq = []
  X = {}
  edges = [(u, v) for u, v in E if {u, v} != {s, t}]
  dir_e = []
  for u, v in edges:
    i = pot[u] - pot[v]
    if i == 0:
      return None
    if i < 0:
      u, v, i = v, u, -i
    dir_e.append((u, v, i, find(left[(u, v)]), find(left[(v, u)])))
  adj = {}
  for u, v, i, L, R in dir_e:
    adj.setdefault(L, []).append((R, i)); adj.setdefault(R, []).append((L, -i))
  start = find(left[(s, t)]) if (s, t) in left else None
  start = next(iter(adj))
  X[start] = Fraction(0); st = [start]
  while st:
    f = st.pop()
    for g, d in adj[f]:
      if g not in X:
        X[g] = X[f] + d; st.append(g)
  for u, v, i, L, R in dir_e:
    if X[R] - X[L] != i:
      return None
    sq.append((i, X[L], pot[v]))
  x0 = min(q[1] for q in sq); y0 = min(q[2] for q in sq)
  W = max(q[1] + q[0] for q in sq) - x0; H = max(q[2] + q[0] for q in sq) - y0
  den = 1
  for q in sq:
    for z in q:
      den = den * z.denominator // np.gcd(den, z.denominator)
  sqi = [(int(a * den), int((b - x0) * den), int((c - y0) * den)) for a, b, c in sq]
  Wi, Hi = int(W * den), int(H * den)
  g = 0
  for a, b, c in sqi:
    g = np.gcd(np.gcd(g, a), np.gcd(b, c))
  g = int(np.gcd(np.gcd(g, Wi), Hi))
  sqi = [(a // g, b // g, c // g) for a, b, c in sqi]
  return sqi, Wi // g, Hi // g

def valid_tiling(sq, W, H):
  if sum(a * a for a, _, _ in sq) != W * H:
    return False
  for (a, x, y), (b, u, v) in itertools.combinations(sq, 2):
    if min(x + a, u + b) > max(x, u) and min(y + a, v + b) > max(y, v):
      return False
  return all(x >= 0 and y >= 0 and x + a <= W and y + a <= H for a, x, y in sq)
