# Analytic step for A101513, n > n0 = 6000 (exact rationals).
# Bounds (valid for rows j >= 5 obeying invariant (I)):
#   l_j <= (210/162)(j + 48)                         (an interval of length l above 7 has
#                                                     >= (162/210) l - 48 composites)
#   l_{n-1} >= n - 49 - (24/162)(n + 46)             (|P_{n-1}| <= primes in an interval of
#                                                     length l_{n-2}/2)
#   R_n <= R_{n0} + sum_{j=n0+1}^{n} (210/162)(j + 48)
# Need l_{n-1}^2 >= R_n for every n > n0. f(n) = LB(n)^2 - UB(n); check f(n0+1) > 0 and
# f(n+1) - f(n) > 0 for all n > n0 (the increment is linear in n, checked at n0+1 with
# positive slope).
from fractions import Fraction as F
n0, R0 = 6000, 18568221
def LB(n): return n - 49 - F(24, 162) * (n + 46)
def UB(n): return R0 + F(210, 162) * sum(j + 48 for j in range(n0 + 1, n + 1))
def f(n): return LB(n) ** 2 - UB(n)
assert LB(n0 + 1) > 0 and f(n0 + 1) > 0
inc = lambda n: (LB(n + 1) ** 2 - LB(n) ** 2) - F(210, 162) * (n + 1 + 48)
# inc(n) = (LB(n+1)-LB(n)) (LB(n+1)+LB(n)) - ..., linear in n:
a = inc(n0 + 2) - inc(n0 + 1)
assert a > 0 and inc(n0 + 1) > 0
for n in range(n0 + 1, n0 + 2000): assert f(n) > 0
print("f(n0+1) =", float(f(n0 + 1)), " increment slope =", float(a), " ok: l_{n-1}^2 >= R_n for all n > 6000")
