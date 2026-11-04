# A004050 / A085634: 2^a + 3^b = 2^c + 3^d with a != c.
# Reduction (see note): writing X = a (larger power of 2), Y = d,
# |2^X - 3^Y| = |2^c - 3^b| <= 4X, and Ellison 1971 leaves X < 12 or
# X in {13,14,16,19,27}.  Enumerate all values with exponents a <= 40, b <= 26.
#
from collections import defaultdict
rep = defaultdict(list)
for a in range(41):
  for b in range(27):
    rep[2 ** a + 3 ** b].append((a, b))
multi = sorted(v for v, r in rep.items() if len(r) > 1)
print("values with two representations:", multi, [rep[v] for v in multi])
# Check the inequality step: for every pair with X <= 40, |2^X - 3^Y| <= 4X only for small X.
#
small = [(X, Y, 2 ** X - 3 ** Y) for X in range(1, 41) for Y in range(0, 27) if abs(2 ** X - 3 ** Y) <= 4 * X]
print("pairs with |2^X-3^Y| <= 4X:", small)
