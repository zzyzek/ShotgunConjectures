# distinct cycles of y -> sigma(phi(y)) reached from seeds n <= N (y_1 = sigma(phi(n)))
import sys
from sympy import totient, divisor_sigma
N=int(sys.argv[1])
f=lambda y:int(divisor_sigma(int(totient(y))))
cyc={}; seen={}
for n in range(1,N+1):
  y=int(divisor_sigma(int(totient(n)))); path=[]; pos={}
  while y not in seen and y not in pos:
    pos[y]=len(path); path.append(y); y=f(y)
  if y in pos:
    c=path[pos[y]:]; key=min(c); cyc[key]=c
    for v in c: seen[v]=key
    path=path[:pos[y]]; key0=key
  else: key0=seen[y]
  for v in path: seen[v]=key0
  cyc.setdefault(key0,None)
cnt={}
for v,k in seen.items(): pass
for k in sorted(cyc):
  c=cyc[k]; full=[]
  for y in c: full+= [y,int(totient(y))]
  print("cycle len %d (in T: %d values) min %d max %d: %s"%(len(c),2*len(c),min(full),max(full), c if len(c)<=8 else str(c[:8])+'...'))
