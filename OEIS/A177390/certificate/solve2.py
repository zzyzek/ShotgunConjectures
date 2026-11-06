# Unitriangular solver (fast): T(n,n)=1, row n of T^(k n) = coefficients of (k n^2 + y)^n.
# Reports, per row, which columns are non-integral.
from fractions import Fraction as F
from math import comb
import sys
k=int(sys.argv[1]); N=int(sys.argv[2])
T=[[F(1)]]
bad_rows=[]
for n in range(1,N+1):
    e=k*n
    target=[F(comb(n,j)*(k*n*n)**(n-j)) for j in range(n+1)]
    # M = T^e restricted to rows < n (exact powers of the known block); row n of T^e = sum_t x T^t ...
    # Compute row n of T^e as linear in row n of T: (T^e)[n] = sum_{a=0}^{e-1} x_aug * T^(e-1-a) where x_aug = row n with diag;
    # simpler: iterate j from n-1 down with vector-matrix products.
    row=[F(0)]*n+[F(1)]
    for j in range(n-1,-1,-1):
        row[j]=F(0)
        v=[F(0)]*(n+1); v[n]=F(1)
        for t in range(e):
            w=[F(0)]*(n+1)
            for i in range(j,n+1):
                if v[i]:
                    Ri = row if i==n else T[i]
                    for c in range(j,i+1): w[c]+=v[i]*Ri[c]
            v=w
        row[j]=(target[j]-v[j])/e
    T.append(row)
    b=[j for j,x in enumerate(row) if x.denominator!=1]
    if b: bad_rows.append((n,b)); print("row",n,"non-integral columns",b, flush=True)
print("done k",k,"N",N,"rows with non-integral entries:",len(bad_rows))
