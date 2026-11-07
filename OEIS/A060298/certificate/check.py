# A060298: count pairs (x, y), x, y >= 2, with x^y of exactly N digits
# (the reading used in the Lean file) and compare with the data for N <= 12.
from math import isqrt
data = [3,12,34,94,263,768,2333,7167,22291,69751,219081,689736,2174856,6864354,21679391]
def iroot(M, y):
    # largest x with x^y <= M
    x = int(round(M ** (1.0 / y)))
    while x ** y > M: x -= 1
    while (x + 1) ** y <= M: x += 1
    return x
def a(N):
    lo, hi = 10 ** (N - 1), 10 ** N
    tot, y = 0, 2
    while 2 ** y < hi:
        # x >= 2 with lo <= x^y < hi
        tot += max(0, iroot(hi - 1, y) - max(1, iroot(lo - 1, y)))
        y += 1
    return tot
assert [a(N) for N in range(1, len(data) + 1)] == data
print("OK", len(data), "terms")
