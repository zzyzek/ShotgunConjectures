# OEIS A136269: a(n) = floor(sum_{i=1..10^n} i^(1/3)).
# 1. Direct sums (math.fsum of correctly rounded cube roots) for n <= 6
#    against the entry data; the distance to the nearest integer is printed
#    to show float error (about 1e-10) cannot matter.
# 2. The proved formula 3/4*10^(4k) + 5*10^(k-1) - 1 against the data
#    for n = 3k = 3, 6, 9, 12, 15.
# 3. The bounds H - 1/4 - 1/36 <= S(M^3) <= H - 1/4 (H = 3M^4/4 + M/2)
#    for M = 1..60.
import math
from fractions import Fraction

data = [1,16,350,7504,161593,3481214,75000049,1615826124,34811916483,
        750000000499,16158260176316,348119162523278,7500000000004999,
        161582601752402051,3481191625209607376,75000000000000049999,
        1615826017523912899040,34811916252095841925154]

def cbrt(i):
    r = round(i ** (1 / 3))
    return float(r) if r ** 3 == i else i ** (1 / 3)

for n in range(7):
    s = math.fsum(cbrt(i) for i in range(1, 10 ** n + 1))
    assert math.floor(s) == data[n], (n, s)
    print("n =", n, "floor", math.floor(s), "frac %.6f" % (s - math.floor(s)))
for k in range(1, 6):
    f = Fraction(3, 4) * 10 ** (4 * k) + 5 * 10 ** (k - 1) - 1
    assert f == data[3 * k], k
for M in range(1, 61):
    s = math.fsum(cbrt(i) for i in range(1, M ** 3 + 1))
    H = 0.75 * M ** 4 + M / 2
    assert H - 0.25 - 1 / 36 - 1e-6 <= s <= H - 0.25 + 1e-6, M
print("OK: data n <= 6, formula n = 3..15, bounds M <= 60")
