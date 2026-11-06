# Power-series check: the closed forms G and K have Taylor coefficients
# [x^tau y^l] G = A(tau,l)/l!  and  [x^tau y^l] K = (B(tau,l) + C(tau,2) A(tau,l))/l!
# (tau,l <= 6), in particular [y^1]G(0,y) = 2 and [y^1]K(0,y) = 0, the two values the
# first-order PDEs leave free.  Then n! [z^(n+1)] K(z,z) = -S_n.
import sympy as sp
from math import factorial, comb
from ab import A,B
x,y,s,q,z=sp.symbols('x y s q z')
N=8
E=sp.series(sp.exp(q*(-x+2*y)),q,0,N+3).removeO().subs(q,1)
EJ=sp.integrate(sp.series(sp.exp(q*(x*(s**2-2*s)+2*y*s)),q,0,N+3).removeO().subs(q,1),(s,0,1))  # E*J, rho = 1 - sigma
G=sp.expand(1+2*y*E-2*x*EJ)
p=6*x**3-2*x**2*y-3*x**2-14*x*y**2+11*x*y+10*y**3
qq=12*x**3*y-16*x**2*y**2-12*x**2*y+24*x*y**2-11*x*y-10*y**3
r=-12*x**4+16*x**3*y+12*x**3+24*x**2*y**2-24*x**2*y+3*x**2-48*x*y**3+12*x*y**2+20*y**4
Kx=sp.expand(p+E*qq+EJ*r)   # = 12 x K
ok=True
for t in range(0,7):
  for l in range(0,7):
    if t+l>N: continue
    a=A(t,l)/factorial(l); k=(B(t,l)+comb(t,2)*A(t,l))/factorial(l)
    if G.coeff(x,t).coeff(y,l)!=sp.Rational(a.numerator,a.denominator): ok=False; print("G",t,l)
    if Kx.coeff(x,t+1).coeff(y,l)/12!=sp.Rational(k.numerator,k.denominator): ok=False; print("K",t,l)
for l in range(0,N): 
  if Kx.coeff(x,0).coeff(y,l)!=0: ok=False; print("K not regular",l)
print("series match:",ok)
Q=sum(z**m/(sp.factorial(m)*(2*m+1)) for m in range(0,15))
Kd=z*(3*Q-sp.exp(z)*(4*z**2-2*z+11)+8)/12
ser=sp.series(Kd,z,0,14).removeO()
for n in range(1,12):
  Sn=-sp.factorial(n)*ser.coeff(z,n+1)
  assert Sn==sp.Rational(2,3)*sp.Rational(n**3-n**2+2*n+1,2*n+1),n
print("diagonal coefficients give the formula for n=1..11; in general -n![z^(n+1)]K(z,z) = (4n^2-6n+11)/12 - 1/(4(2n+1))")
