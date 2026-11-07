# Numerical check (NOT a proof) of the first-level corner decomposition used in
# the README section "Toward the size claims", for k = 2..6, and of the
# strip-process block structure for h = 4..32.
#
# Q(n): quadrant wall process (walls x = 0 and y = 0) = quadrant of the toothpick
# structure at stage n (mirror lemma).  strip(h, j): wall process in
# {x >= 0, 0 <= y <= h} with walls x = 0, y = 0, y = h, started from the half
# toothpick (1,h)-(1,h-1).
#
import sys
from collections import Counter
from wp import run, ends
import sim

def Qrun(n):
  wall = lambda p: p[0] == 0 or p[1] == 0
  init = {((0, 0), (0, 1)): 1, ((0, 1), (1, 1)): 2}
  cov  = Counter({(0, 0): 1, (0, 1): 2, (1, 1): 1})
  return run(wall, init, cov, [((1, 1), 1)], n-2, 2)

def strip(h, j):
  wall = lambda p: p[0] == 0 or p[1] == 0 or p[1] == h
  init = {((1, h-1), (1, h)): 1}
  cov  = Counter({(1, h): 1, (1, h-1): 1})
  return run(wall, init, cov, [((1, h-1), 0)], j-1, 1)

def tf(S, f):
  out = {}
  for (p, q), s in S.items():
    a, b = f(p), f(q); out[(min(a, b), max(a, b))] = s
  return out

def win(S, x0, y0, x1, y1):
  return {g for g in S if x0 <= min(g[0][0], g[1][0]) and max(g[0][0], g[1][0]) <= x1 and
                          y0 <= min(g[0][1], g[1][1]) and max(g[0][1], g[1][1]) <= y1}

def touches(tps, line):
  T = {}
  for c, d, s in tps:
    for e in ends(c, d):
      if line(e): T[e] = min(T.get(e, 10**9), s)
  return T

# Mirror lemma consequence: Q equals the quadrant of the full simulation.
#
for n in (5, 9, 16, 33, 64):
  a, s = sim.run(n)
  quad = {g for g in s if min(g[0][0], g[1][0]) >= 0 and min(g[0][1], g[1][1]) >= 0}
  assert set(Qrun(n)[0]) == quad

# Q at stage 2^(k+1) = Q_k  u  (Q run 2^k stages)+(A,A)  u  its mirror about x = A
#                        u  strip(A, 2^k) shifted by (A-1, 0); with stages.
#
for k in range(2, 7):
  A, off = 2**(k-1), 2**k
  full = dict(Qrun(2**(k+1))[0])
  qk, tq, _, _ = Qrun(2**k)
  T1 = tf({g: s+off for g, s in qk.items()}, lambda p: (p[0]+A, p[1]+A))
  T2 = tf({g: s+off for g, s in qk.items()}, lambda p: (A-p[0], p[1]+A))
  st, ts, _, _ = strip(A, 2**k)
  T3 = tf({g: s+off for g, s in st.items()}, lambda p: (p[0]+A-1, p[1]))
  U = dict(qk)
  for T in (T1, T2, T3):
    for g, s in T.items():
      assert g not in U or U[g] == s
      U[g] = s
  assert U == full
  # Seam y = A (x > A): first-touch stages from the Q copy and from the strip agree.
  #
  a1 = {(x+A, A): s for (x, y), s in touches(tq, lambda p: p[1] == 0 and p[0] > 0).items()}
  a2 = {(x+A-1, A): s for (x, y), s in touches(ts, lambda p: p[1] == A and p[0] > 1).items()}
  assert a1 == a2
  print('k', k, 'corner decomposition and seam profile OK;', 'seam touches', sorted(a1.items()))

# Strip(h) after 2h stages: blocks UL = strip(h/2) shifted up, LR = strip(h/2)
# shifted right, UR = strip(h/2) flipped; LL is a further process type.
#
for m in range(2, 6):
  h = 2**m; H = h//2
  full = set(strip(h, 2*h)[0]); base = win(set(strip(H, 2*H)[0]), 0, 0, H, H)
  loc = lambda B, x0, y0: {((p[0]-x0, p[1]-y0), (q[0]-x0, q[1]-y0)) for p, q in B}
  fy = lambda p: (p[0], H-p[1])
  bfy = {tuple(sorted((fy(p), fy(q)))) for p, q in base}
  UL = loc(win(full, 0, H, H, h), 0, H); UR = loc(win(full, H, H, h, h), H, H); LR = loc(win(full, H, 0, h, H), H, 0)
  assert base <= UL and all(g[0][1] <= 1 and g[1][1] <= 1 for g in UL - base)
  assert bfy <= UR and all(g[0][0] == 0 for g in UR - bfy)
  assert base <= LR and len(LR - base) == 1
  print('h', h, 'strip blocks UL, UR, LR match strip(h/2) up to the seam lines')
