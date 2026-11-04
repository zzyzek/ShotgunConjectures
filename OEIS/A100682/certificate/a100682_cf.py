from decimal import Decimal, getcontext
getcontext().prec=400
beta=Decimal(384)**(Decimal(1)/Decimal(4))
# continued fraction
x=beta; cf=[]
for _ in range(150):
  a=int(x); cf.append(a); x=1/(x-a)
p0,q0,p1,q1=1,0,cf[0],1
cands=set()
for k in range(1,150):
  a=cf[k]
  for j in range(1,a+1):
    cands.add(j*q1+q0)
  p0,q0,p1,q1=p1,q1,a*p1+p0,a*q1+q0
def iroot4(v):
  import math
  r=math.isqrt(math.isqrt(v))
  while r**4>v: r-=1
  while (r+1)**4<=v: r+=1
  return r
exc=[]
for m in sorted(cands):
  for X in (int(m*beta)+1, int(m*beta)+2):
    if X%2==0: continue
    n=(X+3)//2
    if 384*m**4<=X**4 and 24*m**4>n*(n-1)*(n-2)*(n-3):
      exc.append(n)
exc=sorted(set(exc))
print(len(cands), 'candidates; exceptions found:', [e if e<10**12 else 'n~10^%d'%(len(str(e))-1) for e in exc])
print('first new beyond 5318:', [e for e in exc if e>5318][:3])
