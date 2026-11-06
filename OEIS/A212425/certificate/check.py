# Hanna's family A(x) = (x + A(A(x)))^b (A212392: b = 2, A212425: b = 3).
# Computes F to degree D by fixed-point iteration with exact integers, then checks
#  (1) the OEIS data for b = 2, 3;
#  (2) the identity (b+1) I(x) - (b+1) I(F(x)) = u^(b+1) - (b+1) F(x) F(F(x)),
#      u = x + F(F(x)), I = formal antiderivative of F (rational coefficients);
#  (3) the conjecture ((b-1)(n-1)+1) | a(n) for every coefficient up to degree D.
from fractions import Fraction
import sys
def mul(p, q, D):
    r = [0] * (D + 1)
    for i, a in enumerate(p):
        if a:
            for j in range(min(len(q), D + 1 - i)):
                r[i + j] += a * q[j]
    return r
def pw(p, k, D):
    r = [1] + [0] * D
    for _ in range(k): r = mul(r, p, D)
    return r
def comp(p, q, D):
    # p(q(x)), q(0) = 0
    r = [0] * (D + 1); qk = [1] + [0] * D
    for k in range(len(p)):
        if k > 0: qk = mul(qk, q, D)
        if p[k]:
            for i in range(D + 1): r[i] += p[k] * qk[i]
    return r
def solve(b, D):
    F = [0] * (D + 1)
    while True:
        FF = comp(F, F, D)
        u = FF[:]; u[1] += 1
        G = pw(u, b, D)
        if G == F: return F
        F = G
data = {2: [1,2,9,56,400,3096,25256,213832,1861272,16552320,149737632,1373597892],
        3: [1,3,30,406,6336,107415,1922310,35739990,683593902,13364444808]}
for b, D in ((2, 120), (3, 140), (4, 150), (5, 150), (6, 140)):
    F = solve(b, D)
    E = lambda n: (b*b - 1) * (n - 1) + b
    coeffs = [F[E(n)] for n in range(1, 10**6) if E(n) <= D]
    assert all(F[k] == 0 for k in range(D + 1) if k not in {E(n) for n in range(1, len(coeffs) + 1)})
    if b in data:
        assert coeffs[:len(data[b])] == data[b][:len(coeffs)], b
    for n, a in enumerate(coeffs, 1):
        assert a % ((b - 1) * (n - 1) + 1) == 0, (b, n)
    I = [Fraction(0)] + [Fraction(F[k], k + 1) for k in range(D)]
    FF = comp(F, F, D); u = FF[:]; u[1] += 1
    lhs = [(b + 1) * (x - y) for x, y in zip(I, comp(I, F, D))]
    rhs = [x - (b + 1) * y for x, y in zip(pw(u, b + 1, D), mul(F, FF, D))]
    assert lhs == rhs, b
    print("b =", b, "degree", D, ":", len(coeffs), "coefficients, identity and divisibility ok")
