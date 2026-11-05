"""A110034: row sums of the char. polys of the Fibonacci Hankel matrices (F(i+j-1)).
Checks det(I - H_n) (exact, sympy) against the entry's terms and -sum_{k=1..n-1} A061646(k)
for n <= 25; n = 0 gives 1 while the sum is 0.
Run: nice -n 19 python3 check.py"""
import sympy as sp
F = [0, 1]
for _ in range(80): F.append(F[-1] + F[-2])
g = {-1: 1, 0: 1, 1: 1}
for n in range(2, 40): g[n] = 2 * g[n - 1] + 2 * g[n - 2] - g[n - 3]
assert [g[k] for k in range(-1, 14)] == [1, 1, 1, 3, 7, 19, 49, 129, 337, 883, 2311, 6051, 15841, 41473, 108577]
x = sp.Symbol('x')
def a(n):
    if n == 0: return 1
    H = sp.Matrix(n, n, lambda i, j: F[i + j + 1])
    return sp.Poly(H.charpoly(x).as_expr(), x).eval(1)
vals = [a(n) for n in range(26)]
assert vals[:14] == [1, 0, -1, -4, -11, -30, -79, -208, -545, -1428, -3739, -9790, -25631, -67104]
for n in range(1, 26):
    assert vals[n] == -sum(g[k] for k in range(1, n))
    assert g[n] == 2 * F[n] ** 2 + (-1) ** n
print("n=0: |a(0)| =", abs(vals[0]), "but empty sum = 0")
print("OK")
