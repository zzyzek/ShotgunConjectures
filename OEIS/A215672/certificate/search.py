"""A215672 (Coman): every base-2 Fermat pseudoprime P with three or more
prime factors (counted with multiplicity) has a prime factor q with
P = q((r+1)q - r) for a natural number r, i.e. P/q = q + r(q-1).
Reads the Feitsma-Galway list (data/psp2-annot-below-1e13.txt or PSP_DATA)
and lists the counterexamples below the bound (r >= 0 allowed).
Usage: python3 search.py [bound]
"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
path = os.environ.get("PSP_DATA", os.path.join(ROOT, "data", "psp2-annot-below-1e13.txt"))
bound = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
bad = []
for line in open(path):
  t = line.split()
  if not t[0].isdigit():
    t = t[1:]
  P = int(t[0])
  if P >= bound:
    break
  fac = [int(x) for x in t[1:]]
  if len(fac) < 3:
    continue
  if not any(P // q >= q and (P // q - q) % (q - 1) == 0 for q in set(fac)):
    bad.append((P, fac))
print(len(bad), "counterexamples below", bound)
for P, fac in bad[:20]:
  print(P, fac)
