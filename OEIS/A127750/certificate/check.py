# The column recursion t (A111967) against the OEIS data of A127749, A127750, A111982, and the
# inverse property with exact fractions for n <= 200.
from fractions import Fraction as F
N=200
t=[[0]*(N+1) for _ in range(N+1)]
for k in range(N+1):
    for n in range(N+1):
        if n==0: t[n][k]=int(k==0)
        else: t[n][k]=int(n==k)-int(n-1==k)+(t[(n-1)//2][k] if (n-1)%2==0 else 0)
T=[[(2*k+1)*t[n][k] for k in range(n+1)] for n in range(N+1)]
d127749=[1,0,3,0,-3,5,0,3,-5,7,0,0,0,-7,9,0,-3,5,0,-9,11,0,0,0,0,0,-11,13,0,3]
d127750=[1,3,2,5,2,4,2,7,2,4,2,6,2,4,2,9,2,4,2,6,2,4,2,8,2,4,2,6,2,4,2,11,2,4]
d111982=[1,1,2,3,2,4,2,5,2,4,2,6,2,4,2,7,2,4,2,6,2,4,2,8,2,4,2,6,2,4,2,9,2,4]
flat=[x for r in T for x in r]
assert flat[:len(d127749)]==d127749
assert [sum(r) for r in T][:len(d127750)]==d127750
assert [sum(abs(t[n][k]) for k in range(n+1)) for n in range(len(d111982))]==d111982
for n in range(N+1):
    for k in range(N+1):
        s=sum(F(1,2*n+1)*T[j][k] for j in range(min(n,len(T)-1)+1) if j<=n<=2*j and k<=j)
        assert s==(1 if n==k else 0)
print("A127749/A127750/A111982 data match; inverse verified for n,k <= %d"%N)
