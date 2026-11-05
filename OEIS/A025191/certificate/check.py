"""A025191 = A027914(n)-A027914(n-1) = (A081673(n)-A081673(n-1))/2 for n >= 1.
Definitions as in the Lean file; A081673 from its e.g.f. by exact series arithmetic.
Run: nice -n 19 python3 check.py"""
from fractions import Fraction as F
from math import factorial, comb

N = 40
rows = [[1]]
for n in range(1, N):
    p = rows[-1]; q = [0] * (len(p) + 2)
    for i, c in enumerate(p):
        q[i] += c; q[i + 1] += c; q[i + 2] += c
    rows.append(q)
t = lambda n, k: rows[n][k] if (n >= 0 and 0 <= k < len(rows[n])) else 0
T = lambda n, k: t(n, k) - (t(n - 1, k - 1) if n >= 1 and k >= 1 else 0)
a = [sum(T(n, k) for k in range(n + 1)) for n in range(N)]
A027914 = [sum(t(n, k) for k in range(n + 1)) for n in range(N)]
ex = [F(1, factorial(m)) for m in range(N)]
e3 = [F(3 ** m, factorial(m)) for m in range(N)]
I0 = [F(1, factorial(m // 2) ** 2) if m % 2 == 0 else F(0) for m in range(N)]
one_minus = [(1 if m == 0 else 0) - I0[m] for m in range(N)]
prodc = [sum(ex[i] * one_minus[m - i] for i in range(m + 1)) for m in range(N)]
A081673 = [factorial(m) * (e3[m] - prodc[m]) for m in range(N)]
assert a[:15] == [1, 1, 4, 11, 33, 97, 288, 855, 2544, 7577, 22590, 67399, 201215, 601017, 1795966]
assert A027914[:14] == [1, 2, 6, 17, 50, 147, 435, 1290, 3834, 11411, 34001, 101400, 302615, 903632]
assert A081673[:14] == [1, 3, 11, 33, 99, 293, 869, 2579, 7667, 22821, 68001, 202799, 605229, 1807263]
for n in range(1, N):
    assert a[n] == A027914[n] - A027914[n - 1] == (A081673[n] - A081673[n - 1]) / 2
    assert A081673[n] == 2 * A027914[n] - 1
    assert t(n, n) == sum(comb(n, m) * comb(m, m // 2) for m in range(0, n + 1, 2))
print("OK")
