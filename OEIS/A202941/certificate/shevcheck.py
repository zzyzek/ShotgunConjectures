import sys
sys.path.insert(0,'.')
from shev import D
from fractions import Fraction
def vp(x,p):
  x=Fraction(x); v=0
  a,b=x.numerator,x.denominator
  while a%p==0: a//=p; v+=1
  while b%p==0: b//=p; v-=1
  return v
M=int(sys.argv[1])
primes=[q for q in range(3,200) if all(q%r for r in range(2,q))]
for t in (2,3,4):
  Dt=D(t,M+2); fac=lambda n: Dt[n]
  def row(t,p):
    if t==2: return (p-1)//2
    if t==3: return (p-1)//3 if p%3==1 else (2*p-1)//3
    if t==4: return (p-1)//4 if p%4==1 else (p-1)//2
  res=[]
  for p in primes:
    if t==3 and p==3: continue
    n=row(t,p)
    if n>=len(Dt) or n<1: continue
    C=[Fraction(fac(n),fac(m)*fac(n-m)) for m in range(n+1)]
    ok = C[0]==1 and C[n]==1 and all(vp(c,p)>=1 for c in C[1:n])
    integ = all(c.denominator==1 for c in C)
    s=sum(C); rs = (s.denominator%p!=0) and ((s-2)*1).numerator% p==0
    # minimal-row check: v_p(D) zero below the row
    first=[vp(Dt[j],p) for j in range(n+1)]
    res.append((p,n,ok,integ,rs,first[-1],max(first[:-1]) if n>0 else 0))
  print('t',t,[r for r in res if not(r[2] and r[4])] , 'checked',[r[0] for r in res][-3:], len(res), 'nonint rows',[r[0] for r in res if not r[3]][:5])
  print('  vp at row / max below:',[(r[0],r[5],r[6]) for r in res][:14])
