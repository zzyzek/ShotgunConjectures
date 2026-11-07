# A085057: a(n) = squarefree part of (2n)! (Reble's conjecture), by explicit swaps.
# Start A = {n+1..2n}, B = {1..n} (ratio C(2n,n)). For each prime q (decreasing) with k_q = floor(v_q(C(2n,n))/2) >= 1
# pick k_q unused b in (n/q, 2n/q] with b, bq unused, and swap b <-> bq: ratio /= q^2. End ratio = sqfree part.
# Verifies: greedy never runs out, and the final ratio (computed from exponent vectors) equals core((2n)!).
import sys
from sympy import primerange, factorint
def vC(n,q):
  v=0; t=q
  while t<=2*n: v+=(2*n)//t-2*(n//t); t*=q
  return v
def run(n, check):
  used=set(); swaps=[]
  qs=[q for q in primerange(2,int((2*n)**0.5)+2) if q*q<=2*n]
  for q in reversed(qs):
    k=vC(n,q)//2
    b=2*n//q
    while k>0:
      if b<=n//q: return None
      if b not in used and b*q not in used:
        used.add(b); used.add(b*q); swaps.append((b,q)); k-=1
      b-=1
  if check:
    A=set(range(n+1,2*n+1)); B=set(range(1,n+1))
    for b,q in swaps: A.remove(b*q); A.add(b); B.remove(b); B.add(b*q)
    assert len(A)==n and len(B)==n and A|B==set(range(1,2*n+1))
    ex={}
    for x in A:
      for p,e in factorint(x).items(): ex[p]=ex.get(p,0)+e
    for x in B:
      for p,e in factorint(x).items(): ex[p]=ex.get(p,0)-e
    # target exponent: v_p((2n)!) mod 2
    for p in primerange(2,2*n+1):
      vf=0; t=p
      while t<=2*n: vf+=(2*n)//t; t*=p
      assert ex.get(p,0)==vf%2,(n,p)
  return swaps
N1=int(sys.argv[1]); N2=int(sys.argv[2])
for n in range(1,N2+1):
  s=run(n, n<=N1)
  assert s is not None, n
print("greedy succeeds for n <=",N2,"; full exponent check for n <=",N1)
