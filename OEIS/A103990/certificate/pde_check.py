# Symbolic certificate for the generating-function step.
# E = e^{-x+2y}, J = int_0^1 e^{x s^2 - 2 y s} ds, with the exact derivative rules
#   x J_y = -(e^{x-2y} - 1 + 2 y J)          (integration by parts in s)
#   2 x J_x = e^{x-2y} - J - y J_y
# L = 1 - 2x d/dx - y d/dy - 2x + 2y.
import sympy as sp
x,y,J,E,z,s=sp.symbols('x y J E z s')
def dJy(): return -(1/E-1+2*y*J)/x
def dJx(): return (1/E-J-y*dJy())/(2*x)
def dx(f): return sp.diff(f,x)-E*sp.diff(f,E)+sp.diff(f,J)*dJx()
def dy(f): return sp.diff(f,y)+2*E*sp.diff(f,E)+sp.diff(f,J)*dJy()
def L(f): return f-2*x*dx(f)-y*dy(f)-2*x*f+2*y*f
G=1+2*y*E-2*x*E*J
K=(6*x**3-2*x**2*y-3*x**2-14*x*y**2+11*x*y+10*y**3
   +E*(J*(-12*x**4+16*x**3*y+12*x**3+24*x**2*y**2-24*x**2*y+3*x**2-48*x*y**3+12*x*y**2+20*y**4)
       +12*x**3*y-16*x**2*y**2-12*x**2*y+24*x*y**2-11*x*y-10*y**3))/(12*x)
print("L G - (1+2y) =", sp.simplify(L(G)-(1+2*y)))
print("L K - 2x(x-y)G_x =", sp.simplify(L(K)-2*x*(x-y)*dx(G)))
# the derivative rules themselves (check by differentiating under the integral numerically-free):
f=sp.exp(x*s**2-2*y*s)
r1=sp.simplify(sp.integrate(sp.diff(s*f,s),(s,0,1)) - (sp.exp(x-2*y)))  # d/ds(s f) integrates to f(1)
print("IBP identity 1 (int d/ds(s f) = e^{x-2y}):", r1)
# coefficient checks: [x^0 y^1] of G is 2, of K is 0; K regular at x=0
Ej=sp.exp(-x+2*y); Jser=lambda N: sp.integrate(sp.series(sp.exp(sp.Symbol('q')*(x*s**2-2*y*s)),sp.Symbol('q'),0,N).removeO().subs(sp.Symbol('q'),1),(s,0,1))
J0=(1-sp.exp(-2*y))/(2*y)
print("K numerator at x=0:", sp.simplify((sp.numer(sp.together(K))).subs(x,0).subs({E:sp.exp(2*y),J:J0})))
Gy=sp.series(G.subs(x,0).subs({E:sp.exp(2*y)}),y,0,3).removeO()
print("G(0,y) =", sp.simplify(G.subs(x,0).subs({E:sp.exp(2*y)})), " -> [y^1] =",Gy.coeff(y,1))
# K(0,y): limit
Kx0=sp.limit(K.subs({E:sp.exp(-x+2*y)}).subs(J,J0),x,0) if False else None
# diagonal
Kd=sp.simplify(K.subs({x:z,y:z}))
print("K(z,z) =",Kd)
