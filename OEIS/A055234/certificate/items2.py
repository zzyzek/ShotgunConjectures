# Pool: S0-smooth items (from items_S60.json) plus, for each prime q in (S0, N], primes p = q*m -+ 1
# with m S0-smooth (m <= M) and the other neighbour p -+ 1 smooth over primes <= S0 together with Q.
import sys, json
from sympy import isprime, primerange
S0=60; N=int(sys.argv[1]); M=int(sys.argv[2])
base=json.load(open('items_S60.json'))['items']
P0=list(primerange(2,S0+1)); Q=list(primerange(S0+1,N+1)); ALL=P0+Q
def smooth(m,ps):
  for p in ps:
    while m%p==0: m//=p
  return m==1
sm=[1]
for p in P0:
  new=[]
  for m in sm:
    x=m*p
    while x<=M: new.append(x); x*=p
  sm+=new
items=set(tuple(t) for t in base)
for q in Q:
  for m in sm:
    for p,other in ((q*m-1,q*m-2),(q*m+1,q*m+2)):
      if p>S0 and smooth(other,ALL) and isprime(p):
        items.add((p,1))
items=sorted(items)
print(len(sm),"smooth m;",len(items),"items", file=sys.stderr)
json.dump({"S":N,"B":M,"items":items},open("items_Q%d.json"%N,"w"))
