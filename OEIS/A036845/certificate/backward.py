# Exact backward closure for the phi/sigma tug-of-war.  For a bound v, computes the finite set
#   A_phi(v) = { x : applying phi, sigma, phi, ... starting from x reaches a value <= v at some step >= 1 }
# by breadth-first search with exact inverse totient / inverse sigma.  If the search terminates, then
# {n : A036845(n) <= v} = A_phi(v) exactly (A036845(n) = min_k T(n,k), T(n,1) = phi(n)).
import sys
from functools import lru_cache
from sympy import divisors, isprime
sys.setrecursionlimit(10000)
def inv_phi(m):
  # all x with phi(x) = m
  if m==1: return [1,2]
  if m%2: return []
  ps=[d+1 for d in divisors(m) if isprime(d+1)]
  ps.sort(reverse=True)
  res=[]
  def go(rem, i, x):
    if rem==1:
      res.append(x)
      if x%2 and True: pass
      return
    for j in range(i,len(ps)):
      p=ps[j]
      if rem%(p-1): continue
      r=rem//(p-1); pk=p
      while True:
        go(r, j+1, x*pk)
        if r%p: break
        r//=p; pk*=p
  go(m,0,1)
  out=set(res)
  # x odd with phi(x)=m implies 2x too (handled since p=2 has p-1=1: include explicitly)
  return sorted(out)
def inv_phi_full(m):
  base=inv_phi_nop2(m)
  return base
def inv_phi_nop2(m):
  # handle prime 2 separately: phi(2^k * y) = 2^(k-1) phi(y) for k>=1
  if m==1: return [1,2]
  res=set()
  odd=[p for p in (d+1 for d in divisors(m)) if p>2 and isprime(p)]
  odd.sort(reverse=True)
  def go(rem,i,x):
    # x odd part chosen so far; remaining rem to be produced by more odd primes and/or power of 2
    if rem==1: res.add(x); res.add(2*x)
    # power of 2: 2^k contributes 2^(k-1), k>=2 -> rem must be a power of 2 >= 2
    if rem>1 and rem&(rem-1)==0: res.add(x*2*rem)
    for j in range(i,len(odd)):
      p=odd[j]
      if rem%(p-1): continue
      r=rem//(p-1); pk=p
      while True:
        go(r,j+1,x*pk)
        if r%p: break
        r//=p; pk*=p
  go(m,0,1)
  return sorted(res)
def inv_sigma(m):
  if m==1: return [1]
  res=[]
  ds=divisors(m)
  # candidate prime powers p^k with sigma(p^k) = d dividing m
  cands={}
  for d in ds:
    if d==1: continue
    # find p,k with (p^(k+1)-1)/(p-1) = d
    for k in range(1,64):
      # p roughly d^(1/k)
      lo=2; hi=int(round(d**(1.0/k)))+2
      found=False
      for p in range(max(2,hi-3),hi+1):
        s=sum(p**i for i in range(k+1))
        if s==d and isprime(p): cands.setdefault(p,[]).append((k,d)); found=True
      if 2**k>d: break
  primes=sorted(cands)
  def go(rem,i,x):
    if rem==1: res.append(x); return
    for j in range(i,len(primes)):
      p=primes[j]
      for k,d in cands[p]:
        if rem%d==0: go(rem//d,j+1,x*p**k)
  go(m,0,1)
  return sorted(set(res))
def closure(v, limit=10**6):
  # positions: 'P' = value about to have phi applied (seed type), 'S' = value about to have sigma applied
  Aphi=set(); Asig=set(); frontier=[]
  # values w <= v reached by phi (w = phi(x), x in Aphi) or by sigma (w = sigma(x), x in Asig)
  for w in range(1,v+1):
    for x in inv_phi_nop2(w):
      if x not in Aphi: Aphi.add(x); frontier.append(('P',x))
    for x in inv_sigma(w):
      if x not in Asig: Asig.add(x); frontier.append(('S',x))
  while frontier:
    if len(Aphi)+len(Asig)>limit: return None
    t,x=frontier.pop()
    if t=='P':
      # x reached by sigma from y in Asig
      for y in inv_sigma(x):
        if y not in Asig: Asig.add(y); frontier.append(('S',y))
    else:
      for y in inv_phi_nop2(x):
        if y not in Aphi: Aphi.add(y); frontier.append(('P',y))
  return Aphi, Asig
if __name__=="__main__":
  from sympy import totient, divisor_sigma
  # self-test of inverses
  M=300
  tot=[0]*(10*M+11); sg=[0]*(10*M+11)
  for x in range(1,10*M+11): tot[x]=x
  for p in range(2,10*M+11):
    if tot[p]==p:
      for q in range(p,10*M+11,p): tot[q]-=tot[q]//p
  for d in range(1,10*M+11):
    for q in range(d,10*M+11,d): sg[q]+=d
  ip={}; isg={}
  for x in range(1,10*M+11):
    ip.setdefault(tot[x],set()).add(x); isg.setdefault(sg[x],set()).add(x)
  for m in range(1,M):
    assert set(inv_phi_nop2(m))==ip.get(m,set()),m
    assert set(inv_sigma(m))==isg.get(m,set()),m
  print("inverse functions agree with sieve tables for m < %d"%M)
  for v in [int(a) for a in sys.argv[1:]]:
    r=closure(v)
    if r is None: print("v=%d: closure exceeded limit"%v); continue
    Aphi,Asig=r
    print("v=%d: {n : a(n) <= v} has %d elements, max %d"%(v,len(Aphi),max(Aphi)))
