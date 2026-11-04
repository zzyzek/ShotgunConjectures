# Find two perfect squarings of the same rectangle with no common square:
# bucket rectangles by reduced aspect ratio, rescale each pair to a common
# size, compare element sets.  Input: JSON lists from work/GEO-C2.1/search.py.
#
import json, sys
from math import gcd
from itertools import combinations
B = {}
for fn in sys.argv[1:]:
  for sizes, a, b, sq in json.load(open(fn)):
    g = gcd(a, b)
    B.setdefault((a // g, b // g), {})[tuple(sizes)] = (a, b)
same = disjoint = 0
for asp, d in B.items():
  if len(d) < 2:
    continue
  for (s1, (a1, _)), (s2, (a2, _)) in combinations(d.items(), 2):
    L = a1 * a2 // gcd(a1, a2)
    e1 = {x * (L // a1) for x in s1}; e2 = {x * (L // a2) for x in s2}
    same += 1
    if not (e1 & e2):
      disjoint += 1
      if disjoint <= 5:
        print("DISJOINT: rectangle %dx%d" % (asp[0] * L // a1 * a1 // asp[0] if False else L, L * asp[1] // asp[0]),
              "orders", len(s1), len(s2), sorted(e1), sorted(e2))
print("aspect classes with >=2 squarings:", sum(1 for d in B.values() if len(d) > 1), "pairs", same, "disjoint pairs", disjoint)
