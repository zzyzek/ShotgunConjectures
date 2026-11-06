# A068991: recompute members k <= N from the definition (exact fractions), and for squarefree
# members check k | denominator(B_{2k}) via von Staudt-Clausen (den = prod of primes p with
# (p-1) | 2k). Usage: python3 check.py [N]
import sys
from fractions import Fraction
N=int(sys.argv[1]) if len(sys.argv)>1 else 20000
spf=list(range(N+1))
for i in range(2,int(N**.5)+1):
  if spf[i]==i:
    for j in range(i*i,N+1,i):
      if spf[j]==j: spf[j]=i
def fac(n):
  f={}
  while n>1: p=spf[n]; f[p]=f.get(p,0)+1; n//=p
  return f
def sig(n):
  r=1
  for p,e in fac(n).items(): r*= (p**(e+1)-1)//(p-1)
  return r
def phi(n):
  r=n
  for p in fac(n): r=r//p*(p-1)
  return r
def divs(n):
  ds=[1]
  for p,e in fac(n).items(): ds=[d*p**i for d in ds for i in range(e+1)]
  return ds
mem=[k for k in range(1,N+1) if sum(Fraction(sig(d),phi(d)) for d in divs(k)).denominator==1]
data=[1,2,3,6,10,21,30,42,78,110,210,330,390,930,1218,1830,2025,2310,2530,4050,4134,4290,6090,7590,14175,14910]
assert [k for k in mem if k<=14910]==data, mem[:30]
sqf=[k for k in mem if all(e==1 for e in fac(k).values())]
for k in sqf:
  assert all((2*k)%(p-1)==0 for p in fac(k)), k
print(len(mem),"members <=",N,"; data matches;",len(sqf),"squarefree, all satisfy (p-1)|2k for p|k")
