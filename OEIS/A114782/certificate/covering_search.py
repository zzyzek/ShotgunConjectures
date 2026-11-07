from sympy import isprime
from sympy.ntheory.modular import crt
cls=[(2,0,11),(3,0,37),(4,1,101),(6,5,7),(12,7,9901)]
for m in range(12): assert any(m%M==r for M,r,q in cls)
mods=[3]+[q for _,_,q in cls]; res=[1]+[(-pow(10,r,q))%q for M,r,q in cls]
for q,(M,r,_) in zip(mods[1:],cls): assert pow(10,M,q)==1
x,N=crt(mods,res); x=int(x); N=int(N)
p=x
while not isprime(p): p+=N
print("p",p,"N",N, "p%3",p%3)
for k in range(1,200):
    v=10**k+p; assert any(v%q==0 for q in mods[1:]),k
print("ok")
