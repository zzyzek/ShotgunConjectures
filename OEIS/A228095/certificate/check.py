# Kernel vector v_j = (j/p) for Sun's matrices:
#  A228095: [3,3]_p, i,j = 0..p-1, entries ((i^2+3ij+3j^2)/p); v in kernel for p = 5 mod 6.
#  A225611: (6,1)_p, i,j = 1..p-1, entries ((i^2+6ij+j^2)/p); v in kernel for p = 3 mod 4.
# Also: exact determinants for small p, and the elliptic sum S = sum_t ((t^3+6t^2+t)/p) = 0 for p = 3 mod 4.
from sympy import primerange, Matrix
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
for p in primerange(5,600):
    if p%6==5:
        assert all(sum(leg(i*i+3*i*j+3*j*j,p)*leg(j,p) for j in range(p))==0 for i in range(p)), p
    if p%4==3:
        assert all(sum(leg(i*i+6*i*j+j*j,p)*leg(j,p) for j in range(1,p))==0 for i in range(1,p)), p
        assert sum(leg(t**3+6*t*t+t,p) for t in range(p))==0
        assert sum(leg(u**4-6*u*u+1,p) for u in range(p))==-1 and sum(leg(u**4+6*u*u+1,p) for u in range(p))==-1
dets={}
for p in primerange(3,40):
    d1=Matrix(p,p,lambda i,j:leg(i*i+3*i*j+3*j*j,p)).det()
    d2=Matrix(p-1,p-1,lambda i,j:leg((i+1)**2+6*(i+1)*(j+1)+(j+1)**2,p)).det()
    dets[p]=(d1,d2)
    if p%6==5: assert d1==0
    if p%4==3: assert d2==0
print("ok", dets)
