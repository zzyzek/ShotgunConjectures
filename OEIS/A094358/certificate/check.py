# A094358 vs Munafo's congruence 2^^n == 1 (mod n), n <= N.
# 2^^n mod n is computed by the order criterion proved in Lean (munafo_iff): n odd and
# ord_n(2) a power of 2 (n = 1 included). Also compare with the definition of A094358
# (squarefree, every prime divides some Fermat number = ord_p(2) a power of 2).
import sys
from math import gcd
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
def ord2(n):
    k, x = 1, 2 % n
    while x != 1: x = x * 2 % n; k += 1
    return k
def ispow2(k): return k & (k - 1) == 0
spf = list(range(N + 1))
for p in range(2, int(N ** 0.5) + 1):
    if spf[p] == p:
        for q in range(p * p, N + 1, p):
            if spf[q] == q: spf[q] = p
def fac(n):
    f = {}
    while n > 1: p = spf[n]; f[p] = f.get(p, 0) + 1; n //= p
    return f
def tower_mod(n):
    # direct 2^^n mod n for small n via iterated exponent reduction (Euler not needed for n <= 6)
    t = 1
    for _ in range(n): t = pow(2, t)
    return t % n
munafo = [n for n in range(1, N + 1) if n == 1 or (n % 2 == 1 and ispow2(ord2(n)))]
seq = [n for n in range(1, N + 1) if all(e == 1 and p != 2 and ispow2(ord2(p)) for p, e in fac(n).items())]
print('direct 2^^n mod n for n <= 5:', [tower_mod(n) for n in range(1, 6)])
print('n <=', N, ': |Munafo| =', len(munafo), '|A094358| =', len(seq), 'equal:', munafo == seq)
print('first terms:', seq[:20])
