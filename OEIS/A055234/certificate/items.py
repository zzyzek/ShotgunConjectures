# Items (p,k): prime power p^k whose ratio sigma(p^k)/phi(p^k) is S-smooth (as a reduced fraction,
# numerator and denominator S-smooth).  Large p: k = 1 with p-1, p+1 both S-smooth (smooth twin pairs).
import sys, json, heapq
from sympy import isprime, primerange, factorint
from fractions import Fraction
S=int(sys.argv[1]); B=int(sys.argv[2])
PS=list(primerange(2,S+1))
def smooth(m):
  for p in PS:
    while m%p==0: m//=p
  return m==1
# enumerate S-smooth numbers <= B
sm=[1]
for p in PS:
  new=[]
  for m in sm:
    q=m*p
    while q<=B:
      new.append(q); q*=p
  sm+=new
sm=set(sm)
items=[]
for m in sm:
  if m+2 in sm and isprime(m+1):
    p=m+1
    items.append((p,1))
for p in PS:
  for k in range(1,60):
    num=p**(k+1)-1; den=(p-1)**2*p**(k-1)
    fr=Fraction(num,den)
    if smooth(fr.numerator) and smooth(fr.denominator) and (p,k) not in items:
      items.append((p,k))
items=sorted(set(items))
print(len(sm),"smooth numbers;",len(items),"items; largest p",max(p for p,k in items), file=sys.stderr)
json.dump({"S":S,"B":B,"items":items},open("items_S%d.json"%S,"w"))
