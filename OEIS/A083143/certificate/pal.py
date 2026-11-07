# A083143(n): smallest n-digit palindrome divisible by prime(n) (0 if none).
# Ascending first half h = 10^(k-1) + m; residue of the palindrome is linear in the digits of h.
import sys
import numpy as np
from sympy import prime
N=int(sys.argv[1])
data=[2,33,505,1001,10901,101101,1009001,10155101,100121001,1001111001,10000100001,100011110001,1000055500001,10001099010001,100000636000001,1000000330000001,10000002820000001,100000068860000001]
def brute(n,p):
    k=(n+1)//2
    for h in range(10**(k-1),10**k):
        s=str(h); v=int(s+s[::-1][n%2:])
        if v%p==0: return v
    return 0
maxm=0; worst=None
for n in range(1,N+1):
    p=prime(n); k=(n+1)//2; t=n-1
    if n<=12 or p in (2,5):
        v=brute(n,p)
    else:
        w=[(pow(10,t-i,p)+pow(10,i,p))%p if i!=t-i else pow(10,i,p) for i in range(k)]
        D=min(k-1,7)
        ms=np.arange(10**D,dtype=np.int64)
        r=np.full(ms.shape,w[0],dtype=np.int64)
        mm=ms.copy()
        for j in range(D):
            r=(r+(mm%10)*w[k-1-j])%p; mm//=10
        z=np.nonzero(r==0)[0]
        if len(z)==0:
            v=0
            print("NO HIT within 10^D block",n,p,flush=True)
        else:
            m=int(z[0]); h=10**(k-1)+m; s=str(h); v=int(s+s[::-1][n%2:])
            assert v%p==0 and len(str(v))==n and str(v)==str(v)[::-1]
            if m>maxm: maxm=m; worst=(n,p,m)
    if n<=len(data): assert v==data[n-1],(n,v)
    if v==0: print("ZERO",n,p,flush=True)
    if n%500==0: print(n,p,"max m so far",maxm,worst,flush=True)
print("done N=",N,"all nonzero; data matches n<=18; max m",maxm,worst)
