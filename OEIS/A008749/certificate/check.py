# A008749 vs first occurrences in A067628.
# 1. a(n) from the g.f. (coefficient count), 2. p(T) from the Harary-Harborth
# formula (exact integers), compared with the A067628 b-file if given,
# 3. brute-force minimal perimeter of polyiamonds (edge-connected sets of
# triangles) for T <= TMAX, independent of Harary-Harborth.
# Usage: python3 check.py [b067628.txt]
import sys
from math import isqrt
def p(T):
    if T == 0: return 0
    c = isqrt(6*T - 1) + 1
    return c if (c - T) % 2 == 0 else c + 1
N = 400
c = [0]*(N+1)
for j in range(0, N+1, 2):
    for k in range(0, N+1-j, 3):
        for i in range(j+k, N+1): c[i] += 1
a = [c[n] + (c[n-6] if n >= 6 else 0) for n in range(N+1)]
assert a[:20] == [1,1,2,3,4,5,8,9,12,15,18,21,26,29,34,39,44,49,56,61]
first = {}
for T in range(0, a[N] + 10):
    first.setdefault(p(T), T)
for n in range(1, N-1):
    assert p(a[n+2]) == n + 4 and first[n+4] == a[n+2], n
print("conjecture holds for 1 <= n <=", N-2, "(Harary-Harborth formula)")
if len(sys.argv) > 1:
    b = [int(x.split()[1]) for x in open(sys.argv[1]) if x.strip() and not x.startswith('#')]
    assert all(p(T) == b[T] for T in range(len(b)))
    print("formula matches A067628 b-file, T <", len(b))
# brute force: cells (i, j, t), t = 0 up, 1 down
def nbrs(cell):
    i, j, t = cell
    if t == 0: return [(i, j, 1), (i+1, j, 1), (i, j+1, 1)]
    return [(i, j, 0), (i-1, j, 0), (i, j-1, 0)]
def canon(s):
    mi = min(x[0] for x in s); mj = min(x[1] for x in s)
    return frozenset((x[0]-mi, x[1]-mj, x[2]) for x in s)
TMAX = 11
level = {canon([(0, 0, 0)]), canon([(0, 0, 1)])}
for T in range(1, TMAX+1):
    best = min(sum(1 for x in s for y in nbrs(x) if y not in s) for s in level)
    assert best == p(T), (T, best, p(T))
    if T == TMAX: break
    nxt = set()
    for s in level:
        for x in s:
            for y in nbrs(x):
                if y not in s: nxt.add(canon(s | {y}))
    level = nxt
print("brute-force minimal perimeter = formula for 1 <= T <=", TMAX)
