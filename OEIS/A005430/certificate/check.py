"""A005430: inverse binomial transform of n*C(2n,n) equals 2*A132894(n).

Checks, for n < 200: the identity; both sides against [x^(n-1)] (1+x)(1+x+x^2)^(n-1) times 2n;
for n <= 12: the formula sum_k k C(n,k) C(n-k,floor((n-k)/2)) against brute-force enumeration
of H steps in length-n left factors of Motzkin paths (A132894's definition);
that Zudilin's printed formula sum_k k C(n,k) C(2k,k) (-1)^(n-k) equals 2*A132894(n), not A132894(n).
Run: nice -n 19 python3 check.py
"""
from math import comb
from itertools import product

A = lambda n: n * comb(2 * n, n)
inv = lambda n: sum((-1) ** (n - k) * comb(n, k) * A(k) for k in range(n + 1))
f = lambda n: sum(k * comb(n, k) * comb(n - k, (n - k) // 2) for k in range(n + 1))

def coeff(m):
    p = [1]
    for _ in range(m):
        q = [0] * (len(p) + 2)
        for i, c in enumerate(p):
            q[i] += c; q[i + 1] += c; q[i + 2] += c
        p = q
    p = [a + b for a, b in zip(p + [0], [0] + p)]
    return p[m]

for n in range(200):
    assert inv(n) == 2 * f(n)
    if n >= 1:
        assert inv(n) == 2 * n * coeff(n - 1)

def brute(n):
    t = 0
    for w in product('UDH', repeat=n):
        h = 0; ok = True
        for c in w:
            h += {'U': 1, 'D': -1, 'H': 0}[c]
            if h < 0: ok = False; break
        if ok: t += w.count('H')
    return t

for n in range(13):
    assert brute(n) == f(n), n
print("data", [f(n) for n in range(14)])
print("Zudilin formula / A132894:", [inv(n) // f(n) for n in range(1, 8)])
print("OK")
