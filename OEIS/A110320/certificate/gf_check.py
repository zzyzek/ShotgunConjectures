# Compare the A110320 g.f. (offset 1) with sum_{n>=1} (A051292(n+2)-A051286(n+1))/2 z^n,
# using the g.f.s printed in A051292 and A051286 (offset 0).
#
import sympy as sp
z=sp.symbols('z'); R=sp.sqrt(1-2*z-z**2-2*z**3+z**4)
f=(1-z-z**2)/(2*z**2*R)-1/(2*z**2)
g92=(1-z**2+R)/R; g86=1/R
s92=sp.Poly(sp.series(g92,z,0,6).removeO(),z).all_coeffs()[::-1]
s86=sp.Poly(sp.series(g86,z,0,6).removeO(),z).all_coeffs()[::-1]
print("A051292:",s92,"A051286:",s86)
rhs=((g92-s92[0]-s92[1]*z-s92[2]*z**2)/z**2-(g86-s86[0]-s86[1]*z)/z)/2
print("difference:",sp.simplify(f-rhs))
print(sp.series(f,z,0,10))
