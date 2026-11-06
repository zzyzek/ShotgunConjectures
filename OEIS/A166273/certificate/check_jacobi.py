# Brute force: the five identities for m = 12n+7, n < 6000 (needs sympy).
from sympy import jacobi_symbol as J
import itertools
bad=[]
for n in range(0, 6000):
    m=12*n+7
    pre=[0]
    for i in range(1,(m-1)//2+1): pre.append(pre[-1]+J(i,m))
    h6,h3,h2=pre[(m-1)//6],pre[(m-1)//3],pre[(m-1)//2]
    if n%2==0:
        ok = (h3==2*h6) and (h6==h2)
    else:
        ok = (h2==-3*h6) and (h3==-2*h6)
    if not ok: bad.append((n,m,h6,h3,h2))
print(len(bad), bad[:10])
