from math import isqrt
from sympy import primerange
from search_lib import pell
ps=list(primerange(2,40)); tot=0; div=0
for b in ps:
  for d in ps:
    if b==d: continue
    x0,y0=pell(b*d)
    for s in (1,-1):
      if (x0+s)%2: continue
      A=(x0+s)//2; B=(x0-s)//2
      if A%d or B%b: continue
      U2=A//d; V2=B//b; U=isqrt(U2); V=isqrt(V2)
      if U*U!=U2 or V*V!=V2: continue
      tot+=1; hits=[]
      for j in range(60):
        if U%d==0 and V%b==0: hits.append(j)
        U,V = x0*U + b*y0*V, d*y0*U + x0*V
      if hits: div+=1; print(b,d,s,hits[:5])
print(tot,div)
