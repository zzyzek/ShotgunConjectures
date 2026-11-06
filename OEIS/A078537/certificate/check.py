# Builds A078536 from its definition (M(n,0)=1, M(n,n)=1, [M^4](i,j)=M(i+1,j+1)),
# checks M(n,k) = t(n-k, 4^k-1) and row sums = A078537 data; checks the convolution
# identity sum_j t(m-j, A q^j - 1) t(j, b) = t(m, A+b) for q = 2,3,4.
from functools import lru_cache
data=[1,2,6,46,1086,79326,18583582,14481808030,38559135542174]
def run(q,N):
    @lru_cache(None)
    def t(m,c):
        if m==0: return 1
        return sum(t(m-1,q*i) for i in range(c+1)) if c<50 else t(m,c-1)+t(m-1,q*c)
    M=[[0]*N for _ in range(N)]
    for i in range(N): M[i][0]=1; M[i][i]=1
    def mul(A,B): return [[sum(A[i][l]*B[l][j] for l in range(N)) for j in range(N)] for i in range(N)]
    for i in range(N-1):
        P=mul(M,mul(M,mul(M,M))) if q==4 else None
        if q!=4:
            P=M
            for _ in range(q-1): P=mul(M,P)
        for j in range(i+1): M[i+1][j+1]=P[i][j]
    assert all(M[n][k]==t(n-k,q**k-1) for n in range(N) for k in range(n+1))
    for m in range(5):
        for A in range(1,15):
            for b in range(0,15):
                assert sum(t(m-j,A*q**j-1)*t(j,b) for j in range(m+1))==t(m,A+b)
    return [sum(r) for r in M]
rs=run(4,9); assert rs==data, rs
run(2,9); run(3,9)
print("ok", rs)
