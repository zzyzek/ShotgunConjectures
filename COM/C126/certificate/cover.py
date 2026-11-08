from sympy import primerange, n_order
from math import lcm
import sys
for P in (13747,14491,15709):
    par = 1 if P%3==1 else 0  # m parity needed for 3 | P+5^m
    # set of m in [1..L] with 6 | P+5^m : P odd so 2 always divides
    best=None
    data=[]
    for q in primerange(7,2000):
        o=n_order(5,q)
        res=[r for r in range(o) if (P+pow(5,r,q))%q==0]
        if res: data.append((q,o,res))
    # greedy covering of residues m mod L with m ≡ par mod 2
    L=1; chosen=[]
    for q,o,res in sorted(data,key=lambda t:t[1]):
        if o>720: continue
        nl=lcm(L,o)
        if nl>10**6: continue
        chosen.append((q,o,res)); L=nl
    cov=[False]*L
    for m in range(L):
        if m%2!=par: cov[m]=True; continue
        for q,o,res in chosen:
            if m%o in res: cov[m]=True; break
    unc=[m for m in range(L) if not cov[m]]
    print(P, "L",L,"uncovered",len(unc), unc[:10], "primes",[q for q,_,_ in chosen][:20])
