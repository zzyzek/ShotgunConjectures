from math import comb
import sys
def a514(n): return sum(comb(n,k)**2*comb(2*k,k+1) for k in range(n+1))
def a511(n): return sum(comb(n,k)**2*4**k*comb(2*k,k)//(k+1) for k in range(n+1))
def detmod(M,p):
  M=[r[:] for r in M]; n=len(M); d=1
  for c in range(n):
    piv=next((r for r in range(c,n) if M[r][c]%p),None)
    if piv is None: return 0
    if piv!=c: M[c],M[piv]=M[piv],M[c]; d=-d
    d=d*M[c][c]%p; inv=pow(M[c][c],-1,p)
    for r in range(c+1,n):
      f=M[r][c]*inv%p
      if f: M[r]=[(x-f*y)%p for x,y in zip(M[r],M[c])]
  return d%p
for name,f in [('514',a514),('511',a511)]:
  for p in [5,7,11,13]:
    v=[f(n)%p for n in range(2*p-1)]
    print(name,p,v)
