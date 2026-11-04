from sympy import factorint, divisor_sigma, divisor_count
from fractions import Fraction
from itertools import combinations
H=[int(l.split()[1]) for l in open('b001599.txt') if l.strip() and not l.startswith('#')]
Hs=set(H)
def isharm(n,f):
    d=1;s=1
    for p,e in f.items(): d*=e+1; s*=(p**(e+1)-1)//(p-1)
    return (n*d)%s==0, n*d//s if (n*d)%s==0 else None, s
bad_seed=[];powerful=[];deficient=[];h3p=[]
for n in H:
    f=factorint(n); ok,h,s=isharm(n,f); assert ok
    pk=[p**e for p,e in f.items()]
    # harmonic unitary divisors
    hu=[]
    for r in range(0,len(pk)+1):
        for c in combinations(pk,r):
            m=1
            for x in c: m*=x
            if m in Hs: hu.append(m)
    hu=set(hu)
    minimal=[m for m in hu if m>1 and not any(u>1 and u!=m and m%u==0 and m//u % u !=0 and __import__('math').gcd(u,m//u)==1 for u in hu)]
    if n>1 and len(minimal)>1: bad_seed.append((n,sorted(minimal)))
    if n>1 and all(e>=2 for e in f.values()): powerful.append(n)
    if s<2*n: deficient.append(n)
    if h and h%3==0:
        from sympy import isprime
        if isprime(h//3) and s % (divisor_count(n))!=0: h3p.append((n,h))
print("count",len(H),"max",H[-1])
print("non-unique seeds:",bad_seed[:5],len(bad_seed))
print("powerful:",powerful[:5]); print("deficient:",deficient[:5]); print("H=3p non-arithmetic:",h3p[:5])
