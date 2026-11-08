"""Multistart maximisation of the volume of the convex hull of N points on the unit sphere.
Reports the best volumes and the vertex-degree sequence of the hull for each local maximum."""
import sys
import numpy as np
from scipy.spatial import ConvexHull
from scipy.optimize import minimize

N = int(sys.argv[1]); STARTS = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 1)

def pts(x):
  v = x.reshape(N, 3)
  return v / np.linalg.norm(v, axis=1, keepdims=True)

def vol_grad(x):
  # Fixed hull triangulation; volume = sum det(a,b,c)/6 over outward faces, gradient exact.
  #
  P = pts(x)
  h = ConvexHull(P)
  V = 0.0; G = np.zeros_like(P)
  for s in h.simplices:
    a, b, c = P[s]
    d = np.dot(a, np.cross(b, c))
    if d < 0:
      s = s[[0, 2, 1]]; a, b, c = P[s]; d = -d
    V += d / 6
    G[s[0]] += np.cross(b, c) / 6; G[s[1]] += np.cross(c, a) / 6; G[s[2]] += np.cross(a, b) / 6
  # Chain rule through normalisation.
  #
  X = x.reshape(N, 3); r = np.linalg.norm(X, axis=1, keepdims=True)
  Gx = (G - np.sum(G * P, axis=1, keepdims=True) * P) / r
  return V, Gx.ravel()

res = []
for t in range(STARTS):
  x0 = rng.normal(size=3 * N)
  f = lambda x: tuple(-u for u in vol_grad(x))
  r = minimize(f, x0, jac=True, method="BFGS", options={"gtol": 1e-12, "maxiter": 5000})
  P = pts(r.x); h = ConvexHull(P)
  deg = np.zeros(N, int)
  edges = set()
  for s in h.simplices:
    for i in range(3):
      e = tuple(sorted((s[i], s[(i + 1) % 3])))
      edges.add(e)
  for (i, j) in edges: deg[i] += 1; deg[j] += 1
  res.append((h.volume, tuple(sorted(deg)), len(h.simplices), P.tolist()))
res.sort(reverse=True)
seen = {}
import json
json.dump({'N': N, 'volume': res[0][0], 'points': res[0][3]}, open(f'best_{N}.json', 'w'))
for v, d, f, _ in res:
  key = (round(v, 9), d)
  seen[key] = seen.get(key, 0) + 1
for (v, d), c in sorted(seen.items(), reverse=True)[:12]:
  print(f"{v:.12f} deg={d} hits={c}")
