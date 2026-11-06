# A227012: a(n) = floor(M(n)), M(n) = harmonic mean of (n-1)^3+1, ..., n^3.
# Claim: for n >= 3, |M(n) - T(n)| < 1/8 with T(n) = (n - 1/2)^3 + 1/2, hence
# a(n) = floor(T(n)) = ((2n-1)^3 + 4) div 8, a quasi-polynomial of period 4.
#
# Bounds used (A = (n-1)^3, B = n^3, L = B - A, D = A + B + 1, z = L/D, s = H_B - H_A):
#   midpoint rule for the convex 1/x: 1/k <= ln((k+1/2)/(k-1/2)) <= 1/k + 1/(9k^3)  (k >= 1)
#   so V - E <= s <= V, V = ln((B+1/2)/(A+1/2)) = 2 artanh(z), E = 1/(18 A^2)
#   2z(1 + z^2/3) <= V <= 2z(1 + z^2/3 + z^4/(5(1 - z^2)))
#   => L/Vup <= M <= L/(Vlo - E).
# Part 1 (sympy, exact): both rational-function inequalities
#   L/Vup > T - 1/8 and L/(Vlo - E) < T + 1/8 hold for all n >= N0.
# Part 2 (mpmath interval arithmetic): |M(n) - T(n)| < 1/8 for 3 <= n < N0, and the
#   values floor(M(n)) for n = 1..N0 agree with the OEIS data.
import sympy as sp
from mpmath import iv, mp
n = sp.symbols('n', positive=True)
A = (n - 1)**3; B = n**3; L = B - A; D = A + B + 1; z = L / D
T = (n - sp.Rational(1, 2))**3 + sp.Rational(1, 2)
Vup = 2*z*(1 + z**2/3 + z**4/(5*(1 - z**2)))
Vlo = 2*z*(1 + z**2/3)
E = 1 / (18*A**2)
N0 = 12
def holds_from(expr, N0):
    # expr > 0 for all real n >= N0: numerator/denominator sign analysis
    num, den = sp.fraction(sp.together(expr))
    num = sp.Poly(sp.expand(num), n); den = sp.Poly(sp.expand(den), n)
    for P in (num, den):
        roots = [r for r in sp.real_roots(P) if r >= N0]
        if roots: return False
    return bool((num.eval(N0) * den.eval(N0)) > 0)
c1 = holds_from(L/Vup - (T - sp.Rational(1, 8)), N0)
c2 = holds_from((T + sp.Rational(1, 8)) - L/(Vlo - E), N0)
# also Vlo - E > 0 for n >= N0
c3 = holds_from(Vlo - E, N0)
print("analytic bounds for n >=", N0, ":", c1, c2, c3)
assert c1 and c2 and c3
iv.dps = 40
data = [1,4,16,43,91,166,275,422,614,857,1158,1521]
for k in range(1, N0 + 1):
    a, b = (k - 1)**3, k**3
    s = iv.mpf(0)
    for j in range(a + 1, b + 1): s += iv.mpf(1) / j
    M = iv.mpf(b - a) / s
    f = int(mp.floor(M.a)); assert f == int(mp.floor(M.b))
    assert f == data[k - 1], k
    if k >= 3:
        Tk = iv.mpf(2*k - 1)**3 / 8 + iv.mpf(1) / 2
        assert (M - Tk).b < 0.125 and (M - Tk).a > -0.125, k
        assert f == ((2*k - 1)**3 + 4) // 8
print("n = 1 ..", N0, "ok")
