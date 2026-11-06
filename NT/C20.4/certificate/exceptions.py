# Numbers n <= N that are not a sum of exactly three polygonal numbers of positive rank,
# hexagonal r(2r-1) and pentagonal r(3r-1)/2, r >= 1.
import numpy as np, sys
N=int(sys.argv[1])
def exc(f):
  P=[]; r=1
  while f(r)<=N: P.append(f(r)); r+=1
  a=np.zeros(N+1,bool); a[P]=True
  two=np.zeros(N+1,bool)
  for p in P: two[p:]|=a[:N+1-p]
  three=np.zeros(N+1,bool)
  for p in P: three[p:]|=two[:N+1-p]
  return [n for n in range(1,N+1) if not three[n]]
h=exc(lambda r:r*(2*r-1)); p=exc(lambda r:r*(3*r-1)//2)
print("hexagonal: count",len(h),"largest",h[-1])
print("pentagonal: count",len(p),"largest",p[-1])
