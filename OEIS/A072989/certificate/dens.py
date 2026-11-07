# A072989: m with #{x in [1,m]: x^m = 1 mod m} != gcd(m, phi(m)).
# Count via unit-group structure; brute-force check for small m.
import sys
from math import gcd
N=int(sys.argv[1])
spf=list(range(N+1))
i=2
while i*i<=N:
    if spf[i]==i:
        for j in range(i*i,N+1,i):
            if spf[j]==j: spf[j]=i
    i+=1
def fac(m):
    f={}
    while m>1:
        p=spf[m]; f[p]=f.get(p,0)+1; m//=p
    return f
def cnt(m):
    f=fac(m); c=1; ph=1
    for p,e in f.items():
        ph*=(p-1)*p**(e-1)
        if p==2 and e>=3: c*=gcd(m,2)*gcd(m,2**(e-2))
        else: c*=gcd(m,(p-1)*p**(e-1))
    return c,ph
def brute(m): return sum(1 for x in range(1,m+1) if pow(x,m,m)==1%m)
for m in range(1,1500):
    assert cnt(m)[0]==brute(m), m
terms=[];c=0;marks=[10**k for k in range(2,8)]
for m in range(1,N+1):
    a,ph=cnt(m)
    if a!=gcd(m,ph):
        c+=1
        if len(terms)<54: terms.append(m)
    if m in marks: print(m,c,c/m,flush=True)
print(terms)
