# Search consecutive integers both of prime signature {2,3} (p^2 q^3), absent below 3e8 (Myers).
# x = a^2 b^3 and x +- 1 = c^2 d^3: with V = ab, U = cd: d U^2 - b V^2 = +-1. Solutions come from
# eta = U sqrt d + V sqrt b, eta^2 = unit of Z[sqrt(bd)]; we take the fundamental unit eps = x0 + y0 sqrt(bd)
# of norm +1 and test whether eps = eta0^2 (then all solutions are eta0 * eps^j). Then test d | U, b | V,
# U/d, V/b prime and all four primes distinct.
import sys
from math import isqrt
from sympy import primerange, isprime
def pell(D):
  a0=isqrt(D); m,dd,a=0,1,a0; p0,p1=1,a0; q0,q1=0,1
  while True:
    if p1*p1-D*q1*q1==1: return p1,q1
    m=dd*a-m; dd=(D-m*m)//dd; a=(a0+m)//dd
    p0,p1=p1,a*p1+p0; q0,q1=q1,a*q1+q0
PB=int(sys.argv[1]); JMAX=int(sys.argv[2]); found=[]
ps=list(primerange(2,PB))
for b in ps:
  for d in ps:
    if b==d: continue
    x0,y0=pell(b*d)
    # eps = eta0^2: d U0^2 = (x0 + s)/2, b V0^2 = (x0 - s)/2 for s = +-1
    for s in (1,-1):
      if (x0+s)%2: continue
      A=(x0+s)//2; B=(x0-s)//2
      if A%d or B%b: continue
      U2=A//d; V2=B//b; U=isqrt(U2); V=isqrt(V2)
      if U*U!=U2 or V*V!=V2 or 2*U*V!=y0: continue
      for j in range(JMAX):
        if U%d==0 and V%b==0:
          c=U//d; a=V//b
          if len({a,b,c,d})==4 and isprime(c) and isprime(a):
            x=min(d*U*U,b*V*V)
            found.append((b,d,a,c,j,x)); print("FOUND b=%d d=%d a=%d c=%d j=%d digits=%d"%(b,d,a,c,j,len(str(x))),flush=True)
        U,V = x0*U + b*y0*V, d*y0*U + x0*V
print("done",len(found))
