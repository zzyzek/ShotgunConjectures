# A141419: check Sum_{m=1..n} U_{k-1}(cos((2m-1)pi/N))^2 = k(2n-k+1)/2, N = 2n+1, for n <= 40.
from math import cos, pi
def U(r,x):
  a,b=1.0,2*x
  if r==0: return a
  for _ in range(r-1): a,b=b,2*x*b-a
  return b
worst=0
for n in range(1,41):
  for k in range(1,n+1):
    s=sum(U(k-1,cos((2*m-1)*pi/(2*n+1)))**2 for m in range(1,n+1))
    worst=max(worst,abs(s-k*(2*n-k+1)/2))
print("max error",worst)
