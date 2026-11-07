from sympy import isprime, n_order, primerange
import itertools
for p in [48247,56473]:
    # candidate cover primes: small primes with order(10) dividing L
    for L in [6,12,18,24,36,48,60,72]:
        cands=[q for q in primerange(7,10**6) if q not in (2,5) and L % n_order(10,q)==0]
        cov=[]
        for q in cands:
            o=n_order(10,q)
            for a in range(o):
                if (pow(10,a,q)+p)%q==0: cov.append((q,o,a))
        if all(any(r%o==a for q,o,a in cov) for r in range(L)):
            print(p,L,cov); break
    else: print(p,"no cover found")
