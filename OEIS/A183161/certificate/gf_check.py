# Numerical check of the parts of OEIS-A183161 / A218622 / A219197 that are outside Lean, n <= N:
#  (1) Hanna's g.f. formula: with G = 1 + x G^3, B = 1/(1 - 2x G^2 - 3x^2 G^4) has coefficients
#      A183160(n) = sum_k C(n+k, n-k) C(2n-k, k), and G^2 B has coefficients
#      A199033(n) = sum_k C(n+k+1, n-k) C(2n-k+1, k);
#  (2) the self-convolution square roots a (of A183160) and a' (of A199033) are never 3 mod 4,
#      and agree mod 4 with the six-state automaton of OpenProblemsLib/HannaMod4.lean.
# Usage: python3 gf_check.py [N]   (N = 300 takes a few seconds)
import sys
from math import comb
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
def mul(a, b):
    c = [0] * (N + 1)
    for i, x in enumerate(a):
        if x:
            for j in range(N + 1 - i):
                c[i + j] += x * b[j]
    return c
def inv(a):
    r = [0] * (N + 1); r[0] = 1
    for n in range(1, N + 1):
        r[n] = -sum(a[k] * r[n - k] for k in range(1, n + 1))
    return r
def sqrt1(b):
    a = [0] * (N + 1); a[0] = 1
    for n in range(1, N + 1):
        s = b[n] - sum(a[k] * a[n - k] for k in range(1, n))
        assert s % 2 == 0
        a[n] = s // 2
    return a
G = [comb(3 * n, n) // (2 * n + 1) for n in range(N + 1)]
x = [0, 1] + [0] * (N - 1)
G2 = mul(G, G); G4 = mul(G2, G2)
D = [(1 if n == 0 else 0) - 2 * mul(x, G2)[n] - 3 * mul(mul(x, x), G4)[n] for n in range(N + 1)]
assert all(u == v for u, v in zip(G, [1] + mul(x, mul(G2, G))[1:])), "G = 1 + x G^3"
B = inv(D)
B183160 = [sum(comb(n + k, n - k) * comb(2 * n - k, k) for k in range(n + 1)) for n in range(N + 1)]
B199033 = [sum(comb(n + k + 1, n - k) * comb(2 * n - k + 1, k) for k in range(n + 1)) for n in range(N + 1)]
print("A183160 = [x^n] 1/D:", B == B183160)
print("A199033 = [x^n] G^2/D:", mul(G2, B) == B199033)
a = sqrt1(B183160); a2 = sqrt1(B199033)
print("A183161 starts", a[:8], " A219197 starts", a2[:8])
print("A183161 never 3 mod 4:", all(v % 4 != 3 for v in a))
print("A219197 never 3 mod 4:", all(v % 4 != 3 for v in a2))
# The automaton of HannaMod4 (states 0..5, LSB-first binary digits; A183161 starts in 0, A219197 in 1).
d0 = [0, 0, 3, 4, 4, 5]; d1 = [1, 2, 2, 5, 3, 5]; out = [1, 1, 2, 2, 2, 0]
def run(s, n):
    while n:
        s = (d1 if n & 1 else d0)[s]; n >>= 1
    return out[s]
print("automaton = A183161 mod 4:", all(run(0, n) == a[n] % 4 for n in range(N + 1)))
print("automaton = A219197 mod 4:", all(run(1, n) == a2[n] % 4 for n in range(N + 1)))
