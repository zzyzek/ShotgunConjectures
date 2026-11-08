"""Bicapped square antiprism inscribed in the unit sphere: poles (0,0,+-1), squares at
heights +-h rotated by 45 degrees. Volume V(h) as a sum of origin-based tetrahedra,
maximised exactly."""
import sympy as sp
h = sp.symbols('h', positive=True)
r = sp.sqrt(1 - h**2)
N = sp.Matrix([0, 0, 1]); S = sp.Matrix([0, 0, -1])
A = [sp.Matrix([r*sp.cos(sp.pi*k/2), r*sp.sin(sp.pi*k/2), h]) for k in range(4)]
B = [sp.Matrix([r*sp.cos(sp.pi*k/2 + sp.pi/4), r*sp.sin(sp.pi*k/2 + sp.pi/4), -h]) for k in range(4)]
def t(a, b, c):
  d = sp.Matrix.hstack(a, b, c).det()
  return sp.sign(d.subs(h, sp.Rational(3, 10))) * d / 6
V = 0
for k in range(4):
  V += t(N, A[k], A[(k+1) % 4]) + t(S, B[k], B[(k+1) % 4])
  V += t(A[k], A[(k+1) % 4], B[k]) + t(B[k], B[(k+1) % 4], A[(k+1) % 4])
V = sp.simplify(V)
print("V(h) =", V)
dV = sp.simplify(sp.diff(V, h))
sols = sp.solve(sp.Eq(dV, 0), h)
for s in sols:
  if s.is_real and 0 < s < 1:
    print("h* =", sp.nsimplify(s), sp.N(s, 20), "V* =", sp.N(V.subs(h, s), 20), sp.simplify(V.subs(h, s)))
p = sp.Poly(sp.numer(sp.together(dV)), h)
print("numerator of V'(h):", sp.factor(sp.numer(sp.together(dV))))
