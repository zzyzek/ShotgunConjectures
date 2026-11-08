# Full characterisation test against the b-file definition (direct sums), k <= 6000:
# member iff k = 1, or k odd > 1 and all prime factors p share v2(p-1),
# or k = 4m or 8m with m odd, every prime factor of m = 3 mod 4, m > 3 ... (test variants)
from sympy import factorint
from sympy.ntheory import reduced_totient
def v2(x):
  c=0
  while x%2==0: x//=2;c+=1
  return c
def member(k):
  if k==1: return True
  lam=int(reduced_totient(k))
  if lam%2: return False
  L=lam//2
  return sum(pow(j,L,k) for j in range(1,k))%k==0
def hyp(k):
  if k==1: return True
  f=factorint(k); e=f.get(2,0); odd=[p for p in f if p>2]
  if e==0: return len(set(v2(p-1) for p in odd))==1
  if e in (2,3):
    m=k>>e
    lam=int(reduced_totient(k))
    return m>1 and all(p%4==3 for p in odd) and lam//2>=3
  return False
bad=[k for k in range(1,6001) if member(k)!=hyp(k)]
print("mismatch",bad[:30])
