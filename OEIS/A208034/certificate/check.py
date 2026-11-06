# Exact rational recurrence for exp(sum b(n) x^n/n): (n+1)A(n+1) = sum_j b(j+1) A(n-j).
# Checks the A208034 data and conjectures (1)-(3) for k <= 6, n <= 60.
from fractions import Fraction
N=60
P=[0,1]
for n in range(2,N+2): P.append(2*P[-1]+P[-2])
def expc(b):
  A=[Fraction(1)]
  for n in range(N):
    A.append(sum(b(j+1)*A[n-j] for j in range(n+1))/(n+1))
  return A
data=[1,2,6,26,122,602,3062,15906,83906,447842,2412566,13094490,71513210]
A=expc(lambda n:2*P[n]**2); assert A[:len(data)]==data
for k in range(1,7):
  assert all(x.denominator==1 for x in expc(lambda n:2*P[n]**(2*k)))
  assert expc(lambda n:2*P[n]**(2*k-1))[3].denominator!=1
  assert expc(lambda n:P[n]**(2*k))[2].denominator!=1
print("ok")
