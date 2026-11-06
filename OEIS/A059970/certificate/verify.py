# Direct check of both A059970 conjectures for n <= 21 with a non-cached nim product,
# plus the identities used in the proof: x_k^(2^l) = x_k + sum_{i<l} alpha_k^(2^i),
# s_k = x_{k-1} + e2 with e2 in {0,1}, and y(n) = y(n - 2^k) for 1 <= n - 2^k < 2^k.
import sys
from functools import lru_cache
@lru_cache(maxsize=1<<16)
def nmul(a,b):
    if a<2 or b<2: return a*b
    m=max(a,b); k=0
    while (1<<(1<<(k+1)))<=m: k+=1
    h=1<<k; F=1<<h
    a1,a0=a>>h,a&(F-1); b1,b0=b>>h,b&(F-1)
    c11=nmul(a1,b1); c00=nmul(a0,b0)
    c=nmul(a1^a0,b1^b0)^c00
    return (c<<h)^c00^nmul(c11,F>>1)
N=int(sys.argv[1])
r=1; res1={}; res2={}
targets1={2**n-1:n for n in range(1,N+1)}; targets2={2**n+2**(n-1)-1:n for n in range(1,N+1)}
for i in range(1,2**N):
    r=nmul(r,i)
    if i in targets1: res1[targets1[i]]=r
    if i in targets2: res2[targets2[i]]=r
print("(1):",all(v==1 for v in res1.values()),sorted(res1.items())[-1])
print("(2):",all(v==2 for v in res2.values()),sorted(res2.items())[-1])
def y(n):
    r=1
    for c in range(1<<(n-1)): r=nmul(r,(1<<n)^c)
    return r
print("y(n) for n<=",min(N,18),":",[y(n) for n in range(1,min(N,18)+1)])
