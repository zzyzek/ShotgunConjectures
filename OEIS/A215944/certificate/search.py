"""A215944 (Coman): the only base-2 Fermat pseudoprimes divisible by a smaller
base-2 pseudoprime that cannot be written as p((m+1)p - m)((n+1)p - n) are
multiples of 5461 of the form 5461(42k - 13).

Reads the Feitsma-Galway list (data/psp2-annot-below-1e13.txt, or PSP_DATA).
For every psp P below the bound divisible by a smaller psp, tests whether
P = p * A * B with A = p + m(p-1), B = p + n(p-1):
* strict reading: p a prime factor of P, m, n >= 1;
* broad reading: p >= 2 any divisor, m, n >= 0 (A, B >= p, A = B = 1 mod p-1).
Prints the P that fail the broad reading and are not 5461(42k-13).
Usage: python3 search.py [bound]
"""
import os, sys
from itertools import product

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
path = os.environ.get("PSP_DATA", os.path.join(ROOT, "data", "psp2-annot-below-1e13.txt"))
bound = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 13

psps = []
for line in open(path):
  t = line.split()
  if not t[0].isdigit():
    t = t[1:]
  n = int(t[0])
  if n >= bound:
    break
  fac = [int(x) for x in t[1:]]
  psps.append((n, fac))
pspset = set(n for n, _ in psps)


def factor_dict(fac):
  d = {}
  for f in fac:
    d[f] = d.get(f, 0) + 1
  return d


def divisors(fd):
  ds = [1]
  for p, e in fd.items():
    ds = [d * p ** k for d in ds for k in range(e + 1)]
  return sorted(ds)


def ok_form(P, p, ds, mmin):
  """P = p*A*B, A, B = p + m(p-1) with m >= mmin."""
  if P % p:
    return False
  Q = P // p
  q = p - 1
  for A in ds:
    if A * A > Q:
      break
    if Q % A:
      continue
    B = Q // A
    if (A - p) % q == 0 and (B - p) % q == 0 and A >= p + mmin * q and B >= p + mmin * q:
      return True
  return False


cnt = 0
bad = []
for P, fac in psps:
  fd = factor_dict(fac)
  ds = divisors(fd)
  if not any(d in pspset for d in ds if 1 < d < P):
    continue
  cnt += 1
  strict = any(ok_form(P, p, ds, 1) for p in fd)
  broad = strict or any(ok_form(P, p, ds, 0) for p in ds if p >= 2)
  exc = (P % 5461 == 0) and ((P // 5461) % 42 == 29)
  if not strict and not exc:
    bad.append((P, fac, broad))
print("psp below", bound, "divisible by a smaller psp:", cnt)
print("failing the strict reading, not 5461(42k-13):", len(bad))
for P, fac, broad in bad[:40]:
  print(P, fac, "broad-representable" if broad else "NOT representable even broadly")
print("not representable even broadly:", sum(1 for b in bad if not b[2]))
