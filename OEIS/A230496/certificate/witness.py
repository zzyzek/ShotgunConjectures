# A230496 construction check.
# k = 1 + sum_{b<2^t} 2^{M e_b} with {e_b} chosen greedily so that, for every i <= n = 2^t - 1,
# distinct compositions beta of i over the 1+2^t blocks give distinct exponents sum beta_b e_b
# (block 0 has e = 0).  With 2^M larger than every multinomial coefficient, the terms of the
# multinomial expansion of k^i occupy disjoint bit ranges, so popcount(k^i) = sum over compositions
# of s2(multinomial).  The script checks popcount(k^i) directly for the explicit k.
import sys, itertools
pc=lambda x: bin(x).count('1')
def comps(i,r):
  if r==1: yield (i,); return
  for a in range(i+1):
    for c in comps(i-a,r-1): yield (a,)+c
def ok(es,n):
  r=len(es)
  for i in range(1,n+1):
    seen=set()
    for c in comps(i,r):
      s=sum(a*e for a,e in zip(c,es))
      if s in seen: return False
      seen.add(s)
  return True
for t in (1,2,3):
  n=2**t-1
  es=[0]
  cand=1
  while len(es)<2**t+1:
    if ok(es+[cand],n): es.append(cand)
    cand+=1
  M=(2**t+1)**n
  M=M.bit_length()+1
  k=sum(2**(M*e) for e in es)
  par=[pc(k**i)%2 for i in range(1,n+1)]
  print("t=%d n=%d exponents=%s M=%d bits=%d popcount(k)=%d parities k^1..k^n=%s"%(t,n,es,M,k.bit_length(),pc(k),par))
  sys.stdout.flush()
  assert k%2==1 and all(par)
