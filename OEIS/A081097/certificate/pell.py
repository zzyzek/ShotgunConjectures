# Checks the reduction in README.md: for non-square m and 1 <= n < LIM,
# n is a solution iff (m n - 1)^2 - m k^2 is 1 - m or 1 - 2m, k = isqrt(m n^2).
# Also reproduces the A081097 data (m = 5).
from math import isqrt
LIM = 200000
def ok(m, n):
    k = isqrt(m * n * n)
    return m * n * n == n + isqrt(m * n * n * k * k)
def pell(m, n):
    k = isqrt(m * n * n)
    return (m * n - 1) ** 2 - m * k * k in (1 - m, 1 - 2 * m)
for m in range(2, 40):
    if isqrt(m) ** 2 == m: continue
    for n in range(1, LIM):
        assert ok(m, n) == pell(m, n), (m, n)
data = [1,6,23,40,273,1870,7343,12816,87841,602070,2364359,4126648,28284465,193864606,761316191,1328767776,9107509825,62423800998,245141449079,427859097160,2932589879121,20100270056686,78934785287183]
# solutions for m = 5 from the Pell form: walk n up to the last data term
# using the unit 9 + 4 sqrt5 on (X, Y) = (5n - 1, k).
sols = set()
for N in (1 - 5, 1 - 10):
    for Y in range(0, 200):
        X2 = N + 5 * Y * Y
        if X2 >= 0 and isqrt(X2) ** 2 == X2:
            for X in (isqrt(X2), -isqrt(X2)):
                x, y = X, Y
                for _ in range(40):
                    if x > 0 and (x + 1) % 5 == 0 and x < 5 * 10**15: sols.add((x + 1) // 5)
                    x, y = 9 * x + 20 * y, 4 * x + 9 * y
sols = sorted(s for s in sols if s <= data[-1] and ok(5, s))
assert sols == data, sols[:30]
print("OK reduction for m < 40, n < %d; m = 5 Pell orbit gives the 23 data terms" % LIM)
