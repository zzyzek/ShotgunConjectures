# Independent recheck (different method from prodsearch.c): enumerate all
# a <= b <= c with abc <= X, count triples per (product, sum), report the least
# product with >= m triples sharing a sum.
# usage: python3 recheck_small.py X
#
import sys
from collections import Counter

X   = int(sys.argv[1])
cnt = Counter()
a   = 1
while a * a * a <= X:
  b = a
  while a * b * b <= X:
    for c in range(b, X // (a * b) + 1):
      cnt[(a * b * c, a + b + c)] += 1
    b += 1
  a += 1
best = {}
for (P, S), k in cnt.items():
  for m in range(2, k + 1):
    if (m not in best) or (P < best[m]):
      best[m] = P
for m in sorted(best):
  print("m=%d minProd=%d" % (m, best[m]))
