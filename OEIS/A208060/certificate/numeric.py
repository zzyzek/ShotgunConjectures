import math
def a(n):
  s=1; p=1
  for k in range(1,n+1):
    p*=2*(n//k); s+=p
  return s
print([a(n) for n in range(0,10)])
logL=sum(math.log(j)/(j*(j+1)) for j in range(1,10**6))
for n in [10,100,1000,10000]:
  print(n, math.exp(math.log(a(n))/n), 2*math.exp(logL))
