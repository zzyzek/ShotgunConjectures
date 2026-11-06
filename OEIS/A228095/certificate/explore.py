from sympy import primerange, legendre_symbol as L
def psi(x,p): x%=p; return 0 if x==0 else L(x,p)
for p in primerange(7,60):
    if p%4!=3: continue
    S=sum(psi(t*t*t+6*t*t+t,p) for t in range(p))
    print(p,S, end="; ")
print()
# search Mobius maps phi(t)=(a t+b)/(c t+d) with psi(g(phi t)) = -psi(g(t)) for all t (excluding poles), several p
import itertools
ps=[7,11,19,23,31,43]
g=lambda t,p:(t*t*t+6*t*t+t)%p
found=[]
R=range(-4,5)
for a,b,c,d in itertools.product(R,R,R,R):
    if a*d-b*c==0: continue
    ok=True
    for p in ps:
        for t in range(p):
            den=(c*t+d)%p
            if den==0: continue
            u=(a*t+b)*pow(den,-1,p)%p
            if psi(g(u,p),p)!=-psi(g(t,p),p): ok=False;break
        if not ok: break
    if ok: found.append((a,b,c,d))
print(found[:10])
