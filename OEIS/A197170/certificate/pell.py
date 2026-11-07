# Fundamental solution of x^2 - k y^2 = +-4 (k nonsquare) via the continued fraction of sqrt(k)
# and of (1+sqrt k)/2; reported y as in A197170: y/2 if x,y even, else y.
from math import isqrt, gcd
def fund4(k):
  # smallest unit (x+y sqrt k)/2 > 1 with x^2-ky^2 = +-4: search via CF of sqrt(k) for +-1 (gives (2x,2y)),
  # and directly check y small for odd solutions using CF convergents of sqrt(k) as well (odd sols occur only k=5 mod 8? k = 1 mod 4)
  best=None
  # +-1 via CF
  a0=isqrt(k); m,d,a=0,1,a0; p0,p1=1,a0; q0,q1=0,1
  while True:
    if p1*p1-k*q1*q1 in (1,-1): best=(2*p1,2*q1); break
    m=d*a-m; d=(k-m*m)//d; a=(a0+m)//d
    p0,p1=p1,a*p1+p0; q0,q1=q1,a*q1+q0
  if k%4==1:
    # odd solutions x^2-ky^2=+-4 with y odd: convergents of sqrt(k) don't catch them; use CF of (1+sqrt k)/2
    # P,Q form: alpha=(P+sqrt k)/Q starting P=1,Q=2
    P,Q=1,2; p0,p1=0,1; q0,q1=1,0
    for _ in range(10000):
      a=(P+isqrt(k))//Q if Q>0 else None
      a=int((P+k**0.5)/Q)
      # exact floor
      while (a+1)*Q-P>=0 and ((a+1)*Q-P)**2<=k: a+=1
      while a*Q-P>0 and (a*Q-P)**2>k: a-=1
      p0,p1=p1,a*p1+p0; q0,q1=q1,a*q1+q0
      # convergent p1/q1 approximates (1+sqrt k)/2 ; x = 2p1 - q1, y = q1
      x,y=2*p1-q1,q1
      if x*x-k*y*y in (4,-4):
        if y<best[1]: best=(x,y)
        break
      if y>best[1]: break
      P=a*Q-P; Q=(k-P*P)//Q
  return best
def yrep(k):
  x,y=fund4(k)
  return y//2 if (x%2==0 and y%2==0) else y
if __name__=="__main__":
  import sys
  N=int(sys.argv[1]); found={}
  for k in range(2,N):
    if isqrt(k)**2==k: continue
    g=gcd(k,yrep(k))
    if g not in found: found[g]=k
  print([found.get(n) for n in range(1,46)])
