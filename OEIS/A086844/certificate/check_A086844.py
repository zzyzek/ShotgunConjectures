# Check: for z=1..6 and odd m < M, the orbit b(k+1)=floor(r b(k)) stays odd for
# K steps iff floor(r m) is odd; also check recurrence b(k+1)=z b(k)+z b(k-1)-1.
# Exact arithmetic: floor(r x) = (z x + isqrt(D x^2)) // 2, D = z^2+4z.
from math import isqrt
import sys
def fl(z,x):
  D=z*z+4*z
  return (z*x+isqrt(D*x*x))//2
for z in range(1,7):
  bad=0
  for m in range(1,4001,2):
    b=[m,fl(z,m)]
    for k in range(30):
      b.append(fl(z,b[-1]))
      if b[-1]!=z*b[-2]+z*b[-3]-1: bad+=1
    allodd=all(x%2 for x in b)
    if allodd!=(b[1]%2==1): bad+=1
  print("z",z,"mismatches",bad)
# a(n)-4n for z=2 up to large n
z=2;n=0;mx=0;mn=0;out=[]
for m in range(1,2*10**7,2):
  if fl(z,m)%2: 
    n+=1; d=m-4*n
    if d>mx or d<mn:
      mx=max(mx,d);mn=min(mn,d);out.append((n,m,d))
print(out[-12:])
print("data",[m for m in range(1,240,2) if fl(2,m)%2][:20])
