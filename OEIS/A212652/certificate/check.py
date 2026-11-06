# Check A212652 (least M with n = T(M) - T(k), 0 <= k <= M) against the
# b-file, the odd-divisor formula, and the A209260 row construction.
# Usage: python3 check.py b212652.txt b209260.txt
import sys
def T(r): return r*(r+1)//2
def a_def(n):
    M = 1
    while True:
        if any(n == T(M)-T(k) for k in range(M+1)): return M
        M += 1
def a_formula(n):
    return min(n//h + (h-1)//2 for h in range(1, n+1, 2) if n % h == 0)
def bfile(p):
    out = []
    for line in open(p):
        s = line.split()
        if len(s) == 2 and not line.startswith('#'): out.append((int(s[0]), int(s[1])))
    return out
b = bfile(sys.argv[1])
N = 2000
for n, v in b:
    f = a_formula(n)
    assert f == v, (n, f, v)
    if n <= N: assert a_def(n) == v, n
print("A212652 b-file n <=", b[-1][0], "matches formula; n <=", N, "matches definition")
# A209260: rows of A141419 minus earlier rows, read row by row (entries in
# increasing k order, as in A141419).
seen = set(); seq = []; R = 100
for r in range(1, R+1):
    row = [T(r)-T(r-k) for k in range(1, r+1)]
    seq += [x for x in row if x not in seen]
    seen.update(row)
b2 = [v for _, v in bfile(sys.argv[2])]
assert seq[:len(b2)] == b2, "A209260 mismatch"
rowof = {}
seen = set()
for r in range(1, R+1):
    for k in range(1, r+1):
        x = T(r)-T(r-k)
        if x not in seen: rowof[x] = r
    seen.update(T(r)-T(r-k) for k in range(1, r+1))
for n in range(1, R+1):
    assert rowof[n] == a_formula(n), n
print("A209260 first", R, "rows match b-file (", len(b2), "terms ); n <=", R, "in row a(n)")
