# Exact rational check of a counterexample to Fickett's triangle bound (CFG A12):
# K = triangle (-5,0),(5,0),(0,12) (sides 10,13,13, least angle psi with sin(psi/2)=5/13),
# K' = image of K under rotation (cos,sin)=(-5/13,-12/13) then translation (dx,dy).
from fractions import Fraction as F
import sys
K=[(F(-5),F(0)),(F(5),F(0)),(F(0),F(12))]
c,s=F(-5,13),F(-12,13)
dx,dy=F(sys.argv[1]) if len(sys.argv)>1 else F(-3),F(sys.argv[2]) if len(sys.argv)>2 else F(46,10)
K2=[(c*x-s*y+dx,s*x+c*y+dy) for x,y in K]
def orient(T):
    (a,b),(cc,d),(e,f)=T; return (cc-a)*(f-b)-(d-b)*(e-a)
assert orient(K)>0 and orient(K2)>0
def clip(p,q,T):
    t0,t1=F(0),F(1)
    for i in range(3):
        (x1,y1),(x2,y2)=T[i],T[(i+1)%3]; ex,ey=x2-x1,y2-y1
        f0=ex*(p[1]-y1)-ey*(p[0]-x1); f1=ex*(q[1]-y1)-ey*(q[0]-x1); d=f1-f0
        if d==0:
            if f0<=0: return F(0)
            continue
        t=-f0/d
        if d>0: t0=max(t0,t)
        else: t1=min(t1,t)
    return max(F(0),t1-t0)
side=[F(10),F(13),F(13)]
def L(A,B): return sum(clip(A[i],A[(i+1)%3],B)*side[i] for i in range(3))
L1,L2=L(K,K2),L(K2,K)
print("K' vertices",K2); print("L1 =",L1,"L2 =",L2,"L1/L2 =",L1/L2,float(L1/L2),"> 13/5:",L1/L2>F(13,5))
