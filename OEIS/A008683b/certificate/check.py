# Both readings of Granvik's A008683 comment for n = 2..16: columns n, mu(n), det (reading 1), det (reading 2), A074206(n), count (reading 1), count (reading 2). Needs sympy.
import itertools
from sympy import Matrix, mobius
def H(n):
    # ordered factorizations
    if n==1: return 1
    return sum(H(n//d) for d in range(2,n+1) if n%d==0)
def count_perm(M):
    n=len(M)
    # permanent of 0/1 pattern = number of permutations with all entries nonzero (DP over subsets)
    from functools import lru_cache
    @lru_cache(None)
    def f(i,mask):
        if i==n: return 1
        return sum(f(i+1,mask|1<<j) for j in range(n) if not mask>>j&1 and M[i][j]!=0)
    return f(0,0)
for n in range(2,17):
    A=[[1 if (k+1) and (i+1)%(k+1)==0 else 0 for k in range(n)] for i in range(n)]
    A1=[r[:] for r in A]; A1[n-1][n-1]=0; A1[0][n-1]=1         # reading 1
    R=[[1 if (j==0 or (j+1)%(i+1)==0) else 0 for j in range(n)] for i in range(n)]
    R[n-1][n-1]=0                                               # reading 2 (Redheffer, T(n,n)=0)
    d1=Matrix(A1).det(); d2=Matrix(R).det()
    c1=count_perm(A1); c2=count_perm(R)
    print(n, mobius(n), d1, d2, H(n), c1, c2)
