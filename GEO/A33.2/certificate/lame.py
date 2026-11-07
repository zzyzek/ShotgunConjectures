# Five points on |x|^p + |y|^p = 1, p = 2001/1000, near the vertex (1,0) and on one side
# (y > 0), whose conic is a nondegenerate hyperbola.  Rigorous: mpmath interval arithmetic.
# Conic a x^2 + b xy + c y^2 + d x + e y + f = 0 through 5 points: coefficients are the
# signed 5x5 minors of the 5x6 matrix of monomials (Cramer).  Hyperbola iff b^2 - 4ac > 0;
# nondegenerate iff det [[a,b/2,d/2],[b/2,c,e/2],[d/2,e/2,f]] != 0.
import sys
from mpmath import iv, mp, mpf
iv.dps = 120
p = iv.mpf(2001)/1000
def det(M):
    n = len(M)
    if n == 1: return M[0][0]
    s = iv.mpf(0)
    for j in range(n):
        minor = [row[:j]+row[j+1:] for row in M[1:]]
        term = M[0][j]*det(minor)
        s = s + term if j % 2 == 0 else s - term
    return s
def conic(pts):
    rows = [[x*x, x*y, y*y, x, y, iv.mpf(1)] for x, y in pts]
    co = []
    for j in range(6):
        m = [r[:j]+r[j+1:] for r in rows]
        co.append(det(m) if j % 2 == 0 else -det(m))
    return co
def run(t):
    ys = [iv.mpf(t)*k for k in range(1, 6)]
    pts = [(iv.exp(iv.log(1 - iv.exp(p*iv.log(y)))/p), y) for y in ys]
    a, b, c, d, e, f = conic(pts)
    disc = b*b - 4*a*c
    D3 = det([[a, b/2, d/2], [b/2, c, e/2], [d/2, e/2, f]])
    return disc, D3
ok = False
for t in ["1/10", "1/100", "1/1000", "1/10000", "1/100000"]:
    num, den = map(int, t.split("/"))
    disc, D3 = run(iv.mpf(num)/den)
    hyper = disc.a > 0
    nondeg = (D3.a > 0) or (D3.b < 0)
    ell = disc.b < 0
    print(f"y = k*{t}, k=1..5: disc = {iv.nstr(disc,8)}",
          "HYPERBOLA" if hyper else ("ellipse" if ell else "undecided"),
          "nondegenerate" if nondeg else "degeneracy not excluded")
    ok = ok or (hyper and nondeg)
sys.exit(0 if ok else 1)
