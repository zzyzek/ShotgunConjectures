# Symbolic check: a(m,2n+1) = y(n)^2 in Z[m], y(n)=4y(n-1)-m^2 y(n-2), y0=2, y1=8-m^2.
# Both sides satisfy the degree-4 recurrence with char poly
# (X-m^2)^2 (X^2+(2m^2-16)X+m^4) over Z[m], so 4 matching terms suffice.
#
import sympy as sp
m=sp.symbols('m')
a=[-1,4,-13+6*(m-1)+3*(m-1)**2,(m**2-8)**2]
for n in range(4,40): a.append(sp.expand(m**4*a[n-4]+(2*m)**2*a[n-3]-4*a[n-1]))
y=[2,8-m**2]
for n in range(2,20): y.append(sp.expand(4*y[n-1]-m**2*y[n-2]))
print(all(sp.expand(a[2*n+1]-y[n]**2)==0 for n in range(19)))
X=sp.symbols('X')
P=sp.expand((X-m**2)**2*(X**2+(2*m**2-16)*X+m**4))
c=sp.Poly(P,X).all_coeffs()
print(all(sp.expand(sum(c[i]*a[2*(n+4-i)+1] for i in range(5)))==0 for n in range(14)))
