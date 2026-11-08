"""Rigorous lower bound for the maximum volume of an N-vertex polytope inscribed in the unit
sphere from a numerical configuration: each point is rounded to a rational and scaled by
(1 - 1e-12)/|p|_upper so it lies strictly inside the closed unit ball. Moving one vertex
radially outward to the sphere never decreases the hull volume (the hull volume is convex in
each vertex), so the exact volume of the rational hull is a lower bound for the maximum.
Volume = sum over the hull facets (from scipy, orientation fixed exactly) of det/6, computed
in exact rational arithmetic; facets are checked to be supporting planes exactly.
Usage: python3 certify_lb.py best_N.json"""
import sys, json
from fractions import Fraction as Fr
from scipy.spatial import ConvexHull
import numpy as np
d = json.load(open(sys.argv[1])); P = d["points"]; N = d["N"]
Q = []
for p in P:
  v = [Fr(c).limit_denominator(10**15) for c in p]
  n2 = sum(c * c for c in v)
  # scale s with s^2 n2 <= 1: s = (1 - 1e-12) / sqrt_upper(n2)
  r = Fr(float(n2) ** 0.5).limit_denominator(10**15)
  while r * r < n2: r += Fr(1, 10**15)
  s = (1 - Fr(1, 10**12)) / r
  w = [c * s for c in v]
  assert sum(c * c for c in w) <= 1
  Q.append(w)
h = ConvexHull(np.array([[float(c) for c in w] for w in Q]))
def det(a, b, c):
  return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]))
def sub(a, b): return [a[i] - b[i] for i in range(3)]
V = Fr(0)
for s in h.simplices:
  a, b, c = (Q[i] for i in s)
  nrm = [ (b[1]-a[1])*(c[2]-a[2]) - (b[2]-a[2])*(c[1]-a[1]), (b[2]-a[2])*(c[0]-a[0]) - (b[0]-a[0])*(c[2]-a[2]), (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]) ]
  sides = [sum(nrm[k] * (q[k] - a[k]) for k in range(3)) for q in Q]
  if any(t > 0 for t in sides):
    nrm = [-t for t in nrm]; sides = [-t for t in sides]; b, c = c, b
  assert all(t <= 0 for t in sides), "facet not supporting"
  V += det(a, b, c) / 6
print("N", N, "certified volume lower bound", float(V), "(float run gave", d["volume"], ")")
