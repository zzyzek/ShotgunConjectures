# Reading R1: y(k) from the fundamental solution of x^2 - k y^2 = +-4 (unit of the order Z[(k+sqrt k)/2]),
# reported as y/2 when x, y are both even. Explicit k(n) with gcd(k, y(k)) = n for every n:
#   n = 1: k = 2;  n odd >= 3: k = n^4 + 2n;  n = 2 mod 4: k = n^4/4 + n;  n = 0 mod 4: k = 9n^4/4 + 3n.
# Verified against a brute-force minimal solution of x^2 - k y^2 = +-4 (search y = 1, 2, ...).
from math import isqrt, gcd
def kfam(n):
  if n==1: return 2
  if n%2==1: return n**4+2*n
  if n%4==2: return n**4//4+n
  return 9*n**4//4+3*n
def fund4_brute(k,ymax):
  for y in range(1,ymax+1):
    for s in (4,-4):
      t=k*y*y+s
      if t>0 and isqrt(t)**2==t: return (isqrt(t),y)
  return None
for n in range(1,41):
  k=kfam(n)
  # predicted unit: y_rep = n, fundamental solution has Y = 2n (both even) except n=1
  r=fund4_brute(k,2*n+1)
  x,y=r
  yr = y//2 if (x%2==0 and y%2==0) else y
  assert gcd(k,yr)==n,(n,k,r)
print("family ok n<=40 (brute-force fundamental solution)")
