from fractions import Fraction as F
def expser(b,N):
  A=[F(1)]+[F(0)]*N
  for n in range(N):
    A[n+1]=sum(F(b[j+1])*A[n-j] for j in range(n+1))/(n+1)
  return A
N=60
# A165940
A=expser([0]+[F(1,2**(m*m)) for m in range(1,N+1)],N)
a=[A[n]*2**(n*n+n) for n in range(N+1)]
print('A165940 nonint',[n for n in range(N+1) if a[n].denominator!=1],[int(x) for x in a[:9]])
def t(m):
  k=0
  while m%3==0: m//=3; k+=1
  return 1 if k%2==0 else 0
A=expser([0]+[t(m)*3**m for m in range(1,N+1)],N)
print('A174470 nonint',[n for n in range(N+1) if A[n].denominator!=1],[int(x) for x in A[:14]])
