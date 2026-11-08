import sys
N=int(sys.argv[1]); M=8
# a(n) mod 8 via recurrence-free formula, exact ints then reduce (use D-finite recurrence exactly)
a=[1,2,7]
for n in range(3,2*N+2):
    # (n+1)^2 a(n) = (19n^2-8n-6)a(n-1) - 9(11n^2-30n+21)a(n-2) + 81(n-2)^2 a(n-3)
    t=(19*n*n-8*n-6)*a[n-1]-9*(11*n*n-30*n+21)*a[n-2]+81*(n-2)**2*a[n-3]
    assert t%((n+1)**2)==0; a.append(t//(n+1)**2)
am=[x%M for x in a]
from math import comb
assert all(a[n]==sum(comb(n,k)**2*comb(2*k,k)//(k+1) for k in range(n+1)) for n in range(30))
def detmod(n):
    A=[[am[i+j] for j in range(n)] for i in range(n)]; d=1
    for c in range(n):
        piv=next((r for r in range(c,n) if A[r][c]%2==1),None)
        if piv is None: return None
        if piv!=c: A[c],A[piv]=A[piv],A[c]; d=-d
        d=d*A[c][c]%M; inv=pow(A[c][c],-1,M)
        for r in range(c+1,n):
            f=A[r][c]*inv%M
            if f:
                Ar=A[r]; Ac=A[c]
                for j in range(c,n): Ar[j]=(Ar[j]-f*Ac[j])%M
    return d%M
res=[detmod(n+1) for n in range(N+1)]
print("even at",[n for n,r in enumerate(res) if r is None][:10])
print("7mod8 at",[n for n,r in enumerate(res) if r==7][:10])
from collections import Counter; print(Counter(res))
print("".join(str(r) for r in res))
