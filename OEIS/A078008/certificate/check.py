# Stern-Brocot (Farey) tree of (0,1): row n = the 2^n fractions of depth n (row 0 = 1/2).
# Counts fractions with even denominator and compares with A078008 = (2^n + 2(-1)^n)/3.
# Also lists the rows as sorted fractions to show they are the new terms of the Farey/mediant construction.
from fractions import Fraction
row = [(0, 1, 1, 1)]
for n in range(16):
  fr = [Fraction(a + c, b + d) for a, b, c, d in row]
  assert all(f.denominator == b + d for f, (a, b, c, d) in zip(fr, row))
  ev = sum(1 for a, b, c, d in row if (b + d) % 2 == 0)
  a = (2**n + 2*(-1)**n)//3
  if n <= 3: print(n, sorted(fr))
  print(n, len(row), ev, a, ev == a)
  row = [y for (a, b, c, d) in row for y in ((a, b, a + c, b + d), (a + c, b + d, c, d))]
