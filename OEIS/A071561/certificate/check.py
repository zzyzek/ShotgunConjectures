# Proportion of k <= x with a middle divisor (d | k, sqrt(k/2) <= d < sqrt(2k)), compared with Ford's order
# (log y)^-delta (log log y)^-3/2, y = sqrt(x), delta = 1 - (1 + log log 2)/log 2. Data for x = 10^n from
# A071541 (OEIS), recomputed here for n <= 6.
from math import log, isqrt
delta=1-(1+log(log(2)))/log(2)
A071541=[6,43,336,2932,26870,252756,2409731,23169860,224059958,2175865640]
def has_mid(k):
  for d in range(isqrt(k//2),isqrt(2*k)+2):
    if d>0 and k%d==0 and 2*d*d>=k and d*d<2*k: return True
  return False
c=0; nxt=10; n=1
for k in range(1,10**6+1):
  c+=has_mid(k)
  if k==nxt: assert c==A071541[n-1],(k,c); nxt*=10; n+=1
for n,v in enumerate(A071541,1):
  x=10**n; y=x**0.5
  print(n, v/x, (log(y))**-delta*(log(log(y)))**-1.5 if y>3 else None)
