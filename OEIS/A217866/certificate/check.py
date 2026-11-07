# Recompute A217865 (first differences of floor(n log n)) and check that every
# occurrence of v precedes every occurrence of v+2, for n < 10^6, and print the
# first/last occurrence tables (A217976, A217866) for comparison with OEIS.
# Floating point; values of n log n near an integer are rechecked with mpmath.
import math
from mpmath import mp, mpf, log, floor
mp.dps = 40
N = 10**6
def fl(n):
    x = n * math.log(n) if n > 0 else 0.0
    if n > 0 and abs(x - round(x)) < 1e-6:
        return int(floor(mpf(n) * log(mpf(n))))
    return math.floor(x)
F = [fl(n) for n in range(N + 2)]
d = [F[n + 1] - F[n] for n in range(N + 1)]
first, last = {}, {}
for n in range(1, N + 1):
    first.setdefault(d[n], n); last[d[n]] = n
assert d[1:12] == [1,2,2,3,2,3,3,3,4,3,3]
print("A217976 first:", [first[v] for v in sorted(first)])
print("A217866 last :", [last[v] for v in sorted(last) if last[v] < N - 10**5])
ok = all(last[v] < first[v + 2] for v in first if v + 2 in first)
print("last(v) < first(v+2) for all v seen:", ok)
