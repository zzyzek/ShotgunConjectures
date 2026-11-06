# exp(sum q^(n^m) x^n/n): integral for small q, m; q=2, m=3 matches A158110 data.
from fractions import Fraction as F
def expser(b,N):
  A=[F(1)]+[F(0)]*N
  for n in range(N):
    A[n+1]=sum(F(b[j+1])*A[n-j] for j in range(n+1))/(n+1)
  return A
ok=True
for q in range(0,6):
  for m in range(0,4):
    N=10 if m<3 else 7
    A=expser([0]+[q**(n**m) for n in range(1,N+1)],N)
    ok &= all(x.denominator==1 for x in A)
print('all integral',ok)
print([int(x) for x in expser([0]+[2**(n**3) for n in range(1,6)],5)])
