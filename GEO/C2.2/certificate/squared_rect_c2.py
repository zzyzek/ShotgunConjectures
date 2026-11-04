# C2 (Moron): is there a perfect squared rectangle with coprime sides in which no
# square has a perfect-square side?  Random search: random 3-connected planar graphs
# (convex hulls of random points on a sphere), one edge removed as the "battery",
# Kirchhoff currents (unit resistances) give a squared rectangle (Brooks-Smith-Stone-Tutte).
import numpy as np, sympy as sp, random, math
from math import gcd, isqrt
from functools import reduce
from scipy.spatial import ConvexHull
rnd = random.Random(7)
def rect_from(n, edges, s, t):
    E = [e for e in edges if set(e) != {s, t}]
    idx = [v for v in range(n) if v != t]
    pos = {v: i for i, v in enumerate(idx)}
    L = sp.zeros(n - 1, n - 1)
    for u, v in E:
        for a, b in ((u, v), (v, u)):
            if a != t:
                L[pos[a], pos[a]] += 1
                if b != t:
                    L[pos[a], pos[b]] -= 1
    rhs = sp.zeros(n - 1, 1); rhs[pos[s]] = 1
    x = L.LUsolve(rhs)
    pot = lambda v: 0 if v == t else x[pos[v]]
    el = [abs(pot(u) - pot(v)) for u, v in E]
    if any(e == 0 for e in el):
        return None
    W, H = sp.Integer(1), pot(s)
    den = reduce(sp.ilcm, [sp.fraction(q)[1] for q in el + [H]])
    eli = [int(q * den) for q in el]; Wi, Hi = int(W * den), int(H * den)
    g = reduce(gcd, eli + [Wi, Hi])
    return sorted(e // g for e in eli), Wi // g, Hi // g
found = 0; tried = 0
seen = set()
for it in range(4000):
    n = rnd.randint(6, 10)
    P = np.array([[rnd.gauss(0, 1) for _ in range(3)] for _ in range(n)])
    hull = ConvexHull(P)
    edges = set()
    for simp in hull.simplices:
        for i in range(3):
            a, b = sorted((simp[i], simp[(i + 1) % 3]))
            edges.add((int(a), int(b)))
    # randomly delete some edges from the triangulation, keep 3-connected (checked loosely)
    edges = list(edges)
    if len(set(v for e in edges for v in e)) != n:
        continue
    s, t = edges[rnd.randrange(len(edges))]
    r = rect_from(n, edges, s, t)
    tried += 1
    if r is None:
        continue
    el, W, H = r
    if len(set(el)) != len(el):
        continue
    key = (tuple(el), min(W, H))
    if key in seen:
        continue
    seen.add(key)
    sq = [e for e in el if isqrt(e) ** 2 == e]
    if gcd(W, H) == 1 and not sq:
        print("COUNTEREXAMPLE order", len(el), "rect", W, "x", H, "squares", el)
        found += 1
        if found >= 3:
            break
print("tried", tried, "distinct perfect rectangles", len(seen))
