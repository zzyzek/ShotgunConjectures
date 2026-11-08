"""Minimum-product prime set S and residues x mod p (p in S) such that, for every b mod L,
some p in S divides x - 2^b and some p in S divides x + 2^b (single covering of both signs).
Primes: primitive prime divisors < PMAX of 2^d - 1 for d | L (from PARI partial factoring).
Usage: python3 ilp.py L PMAX [time_limit]"""
import sys, math, subprocess, json
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

L = int(sys.argv[1]); PMAX = int(sys.argv[2]); TL = float(sys.argv[3]) if len(sys.argv) > 3 else 600

def primes_for(L, pmax):
  gp = ("L=%d; P=%d; fordiv(L,d, if(d>1, f=factor(2^d-1, P)[,1]; "
        "for(i=1,#f, q=f[i]; if(q<P && isprime(q) && znorder(Mod(2,q))==d, print(q,\" \",d)))))") % (L, pmax)
  out = subprocess.run(["gp", "-q", "-D", "recover=0"], input=gp, capture_output=True, text=True, timeout=600).stdout
  assert "***" not in out
  res = sorted({(int(a), int(b)) for a, b in (ln.split() for ln in out.strip().splitlines())})
  return res

def solve(L, plist, mult=1):
  var = []
  for (p, m) in plist:
    if m % 2 == 0:
      for c in range(m): var.append((p, m, c, 0))
    else:
      for c in range(m):
        var.append((p, m, c, -1)); var.append((p, m, c, 1))
  nv = len(var); nb = 2 * L
  A = lil_matrix((nb + len(plist), nv))
  pidx = {p: i for i, (p, m) in enumerate(plist)}
  for j, (p, m, c, s) in enumerate(var):
    if s in (0, -1):
      for b in range(c, L, m): A[b, j] = 1
    if s == 0:
      for b in range((c + m // 2) % m, L, m): A[L + b, j] = 1
    if s == 1:
      for b in range(c, L, m): A[L + b, j] = 1
    A[nb + pidx[p], j] = 1
  lo = np.concatenate([np.full(nb, mult), np.zeros(len(plist))])
  hi = np.concatenate([np.full(nb, np.inf), np.ones(len(plist))])
  cost = np.array([math.log10(p) for (p, m, c, s) in var])
  r = milp(cost, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=np.ones(nv), bounds=Bounds(0, 1),
           options={"time_limit": TL, "disp": False})
  if r.x is None:
    return None, r
  chosen = [var[j] for j in range(nv) if r.x[j] > 0.5]
  return chosen, r

plist = primes_for(L, PMAX)
print("L", L, "primes", len(plist), plist[:40])
mult = int(sys.argv[4]) if len(sys.argv) > 4 else 1
chosen, r = solve(L, plist, mult)
if chosen is None:
  print("no solution", r.message)
else:
  print("status", r.message, "log10 product", round(r.fun, 3), "bound", getattr(r, "mip_dual_bound", None))
  print(json.dumps(chosen))
