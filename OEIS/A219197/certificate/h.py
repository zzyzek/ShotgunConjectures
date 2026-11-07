# A199033(n) = sum_k C(n+k+1,n-k) C(2n-k+1,k) equals [t^n] (1-t)^(-2n-3) (1+t)^(-1)
# = sum_j (-1)^j C(3n+2-j, n-j)  (Lagrange inversion of x = t(1-t)^2 applied to 1/((1-t)^2(1-3t)(1+t))).
from math import comb
bad=0
for n in range(0,401):
  lhs=sum(comb(n+k+1,n-k)*comb(2*n-k+1,k) for k in range(n+1))
  rhs=sum((-1)**j*comb(3*n+2-j,n-j) for j in range(n+1))
  if lhs!=rhs: bad+=1
print("A199033 identity failures n<=400:", bad)
