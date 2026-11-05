"""A024187 vs A001711: e_n(3,...,n+3) = [x^1] prod_{r=0..n} (x+3+r) = A001711(n); data check.
Run: nice -n 19 python3 check.py"""
from itertools import combinations
from math import prod, factorial
from fractions import Fraction

def e(n): return sum(prod(c) for c in combinations(range(3, n + 4), n))
def coeff1(n):
    p = [1]
    for r in range(n + 1):
        c = 3 + r
        q = [0] * (len(p) + 1)
        for i, a in enumerate(p):
            q[i] += c * a; q[i + 1] += a
        p = q
    return p[1]
data = [7, 47, 342, 2754, 24552, 241128, 2592720, 30334320, 383970240, 5231113920]
assert [e(n) for n in range(1, 11)] == data
for n in range(40):
    assert coeff1(n) == (factorial(n + 3) // 2) * Fraction(1) * sum(Fraction(1, 3 + s) for s in range(n + 1))
    if n <= 12: assert e(n) == coeff1(n)
print("OK")
