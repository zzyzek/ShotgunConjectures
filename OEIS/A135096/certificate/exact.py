# Exact failure sets: for n in [3, N], the c in [C0, C1] such that n != floor(m^c) + p
# for all m >= 0 and primes p.  Pieces between consecutive breakpoints log(v)/log(m).
import sys
from mpmath import mp, mpf, log, floor, power
from sympy import isprime
mp.dps = 40
N = int(sys.argv[1]); C0 = mpf(sys.argv[2]); C1 = mpf(sys.argv[3])
bps = set()
for m in range(2, N + 1):
    for v in range(2, N + 1):
        c = log(v) / log(m)
        if C0 < c < C1: bps.add(c)
bps = sorted(bps)
pts = [C0] + bps + [C1]
fail = {}
def bad(n, c):
    m = 0
    while True:
        x = 0 if m == 0 else int(floor(power(m, c)))
        if x > n - 2: return True
        if isprime(n - x): return False
        m += 1
res = []
for i in range(len(pts) - 1):
    a, b = pts[i], pts[i + 1]
    if b - a < mpf(10) ** -30: continue
    c = (a + b) / 2
    fl = [n for n in range(3, N + 1) if bad(n, c)]
    res.append((a, b, fl))
# merge
cur = None
for a, b, fl in res:
    key = tuple(fl)
    if cur and cur[2] == key: cur[1] = b
    else:
        if cur: print(mp.nstr(cur[0], 20), mp.nstr(cur[1], 20), list(cur[2]))
        cur = [a, b, key]
print(mp.nstr(cur[0], 20), mp.nstr(cur[1], 20), list(cur[2]))
