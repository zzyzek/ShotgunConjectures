"""A218483: numerical check of Coman's conjectures on the Feitsma-Galway list
(data/psp2-annot-below-1e13.txt or PSP_DATA) below a bound: for every base-2
psp P and prime factor p, P = 8pn + p^2 (n integer) iff P = 1 mod 8; no psp
is 15 mod 40; for P = p1 p2, P = 8 p1 n + p1^2 implies P = 8 p2 (-n) + p2^2.
Usage: python3 check.py [bound]
"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
path = os.environ.get("PSP_DATA", os.path.join(ROOT, "data", "psp2-annot-below-1e13.txt"))
bound = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 10
cnt = 0
for line in open(path):
  t = line.split()
  if not t[0].isdigit():
    t = t[1:]
  P = int(t[0])
  if P >= bound:
    break
  fac = [int(x) for x in t[1:]]
  cnt += 1
  assert P % 40 != 15
  for p in set(fac):
    rep = (P - p * p) % (8 * p) == 0
    assert rep == (P % 8 == 1), (P, p)
  if len(fac) == 2 and (P - fac[0] ** 2) % (8 * fac[0]) == 0:
    n = (P - fac[0] ** 2) // (8 * fac[0])
    assert P == 8 * fac[1] * (-n) + fac[1] ** 2
print("checked", cnt, "pseudoprimes below", bound, "OK")
