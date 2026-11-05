"""A108863: Motzkin transform (x -> x M(x)) of 0,0,0,A001651 vs the entry's terms, the printed g.f.,
and brute-force counts of Dyck n-paths with exactly one UUUD (n <= 11); also the polynomial
identity used in the Lean proof (quotient q). Run: nice -n 19 python3 check.py"""
from itertools import product
import sympy as sp

N = 25
M = [1, 1]
for n in range(2, N): M.append(M[n - 1] + sum(M[k] * M[n - 2 - k] for k in range(n - 1)))
mul = lambda p, q: [sum(p[i] * q[n - i] for i in range(n + 1)) for n in range(N)]
y = [0] + M[:N - 1]
nd3 = [m for m in range(1, 100) if m % 3][:N]
assert all(nd3[m - 1] == (3 * m - 1) // 2 for m in range(1, N))
b = [0, 0, 0] + nd3[:N - 3]
acc = [0] * N; yk = [1] + [0] * (N - 1)
for k in range(N):
    acc = [acc[i] + b[k] * yk[i] for i in range(N)]; yk = mul(yk, y)
data = [0,0,0,1,5,21,78,274,927,3061,9933,31824,100972,317942,995088,3099105]
assert acc[:16] == data

def dyck(n):
    r = 0
    for w in product('UD', repeat=2 * n):
        h = 0; ok = True
        for c in w:
            h += 1 if c == 'U' else -1
            if h < 0: ok = False; break
        if ok and h == 0:
            s = ''.join(w)
            if sum(1 for i in range(len(s) - 3) if s[i:i + 4] == 'UUUD') == 1: r += 1
    return r
assert [dyck(n) for n in range(12)] == data[:12]

x, Y = sp.symbols('x y')
Ms = (1 - x - sp.sqrt(1 - 2 * x - 3 * x ** 2)) / (2 * x ** 2)
G = (x - 1 + (1 - 2 * x) * Ms) / (x * (1 - 3 * x) * (1 + x * Ms))
ser = sp.series(G, x, 0, 16).removeO()
assert [ser.coeff(x, n) for n in range(16)] == data
lhs = x ** 2 * (1 - 3 * x) * Y ** 3 * (1 + Y + Y ** 2)
rhs = (x ** 2 - x + (1 - 2 * x) * Y) * (1 - Y) ** 2
h = x * Y ** 2 + x * Y + x - Y
q, r = sp.div(sp.expand(lhs - rhs), sp.expand(h), Y)
assert r == 0
print("q =", sp.expand(q))
print("OK")
