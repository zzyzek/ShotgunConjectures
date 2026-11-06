# Checks certificate/rle.py (generic minimal-code search) against the OEIS b-files
# b227368.txt, b227761.txt (n <= 132), and fast.py (closed-form model) against
# rle.py for n <= 600. Usage: python3 compare.py <dir with b-files> 600
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rle, fast
bdir, M = sys.argv[1], int(sys.argv[2])
def bfile(name):
  return {int(l.split()[0]): int(l.split()[1]) for l in open(os.path.join(bdir, name)) if l.strip() and l[0] != '#'}
b368, b761 = bfile('b227368.txt'), bfile('b227761.txt')
bad = 0
twos = []
for N in range(M + 1):
  runs, L = rle.code(N)
  v = rle.a761(N)
  if N in b368 and (b368[N] != rle.tonum(runs) or b761[N] != v): bad += 1
  if N >= 2:
    (_, m, k, D, r), _ = fast.best(N)
    if max([x - 1 for x in r[:-1]] + [0]) != v: bad += 1
  if v > 2: bad += 1
  if v == 2: twos.append(N)
pred = [(n + 1) ** 2 - 2 - n % 2 for n in range(2, 60) if (n + 1) ** 2 - 2 - n % 2 <= M]
print("mismatches", bad, "positions of 2 match A227786:", twos == pred)
