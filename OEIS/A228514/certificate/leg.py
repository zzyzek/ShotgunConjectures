import sys
sys.path.insert(0,'.')
from hk import detmod
from math import factorial
def L(a,p):
  a%=p
  return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def primes(N): return [q for q in range(3,N) if all(q%r for r in range(2,int(q**.5)+1))]
bad=[]
for p in primes(260):
  h=(p-1)//2
  # A227609: size h, i,j=1..h, (i^2+j^2)/p ; claim p∤a and (-a/p)=1
  d=detmod([[L(i*i+j*j,p) for j in range(1,h+1)] for i in range(1,h+1)],p)
  if not (d and L(-d,p)==1): bad.append(('609',p))
  # A227968: size h+1, i,j=0..h ; 2a QR
  d=detmod([[L(i*i+j*j,p) for j in range(h+1)] for i in range(h+1)],p)
  if not (d and L(2*d,p)==1): bad.append(('968',p))
  # A227971: size h+1, (i+j)/p
  d=detmod([[L(i+j,p) for j in range(h+1)] for i in range(h+1)],p)
  t=(factorial(h)%p if p%4==1 else L(2,p)%p)
  if d!=t%p: bad.append(('971',p))
  # A228005: size h, i,j=1..h, (i^2+j^2+1)/p ; (a/p) = ((2(-1)^h-4)/p)
  if p>3:
    d=detmod([[L(i*i+j*j+1,p) for j in range(1,h+1)] for i in range(1,h+1)],p)
    if L(d,p)!=L(2*(-1)**h-4,p): bad.append(('005',p,d))
print('bad',bad)
