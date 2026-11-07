# COM-P126 / COM-P127 scan of the Feitsma-Galway base-2 pseudoprime list below 1e13.
# P126: Poulet P = d(d+1)/2 with d a prime factor of P.
# P127: Poulet P2 = 2*P1 - 1 with P1 also Poulet.
# Run: nice -n 19 python3 scan.py   (data file: see DATA.md; env PSP_DATA overrides)
#
import os
DATA = os.environ.get('PSP_DATA',
  os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'data', 'psp2-annot-below-1e13.txt'))
psp = {}
for line in open(DATA):
  t = line[2:].split()
  psp[int(t[0])] = [int(x) for x in t[1:]]
tri, dbl = [], []
for n, fs in psp.items():
  for d in set(fs):
    if d * (d + 1) // 2 == n:
      tri.append((n, d))
  if (n + 1) % 2 == 0 and (n + 1) // 2 in psp:
    dbl.append((n, (n + 1) // 2))
tri.sort(); dbl.sort()
print("P126 count below 1e13:", len(tri))
print("P126 first 10:", tri[:10])
print("P127 count below 1e13:", len(dbl))
print("P127 first 10:", dbl[:10])
