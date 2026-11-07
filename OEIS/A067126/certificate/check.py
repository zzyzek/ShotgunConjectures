# (1) direct: all terms n <= N0 of A067126 (phi(n) >= phi(k) for all k < n), list composite ones.
# (2) record gaps: with A002386 (first prime of record gap) and A005250 (record gaps), check
#     g_k < isqrt(p_k + 1) for every record from index K on; then by A067126_gap no composite term n with
#     prevprime(n) >= p_K and n < 2^64 (record list exhaustive below 2^64).
import math, sys
N0=int(sys.argv[1])
phi=list(range(N0+1))
for p in range(2,N0+1):
  if phi[p]==p:
    for m in range(p,N0+1,p): phi[m]-=phi[m]//p
mx=-1; comp=[]
isprime=lambda n: n>1 and phi[n]==n-1
for n in range(1,N0+1):
  if phi[n]>=mx:
    if not isprime(n) and n>1: comp.append(n)
    mx=phi[n]
print("composite terms <= %d:"%N0, comp)
P=[int(l.split()[1]) for l in open('b002386.txt') if l.strip() and not l.startswith('#')]
G=[int(l.split()[1]) for l in open('b005250.txt') if l.strip() and not l.startswith('#')]
bad=[(i+1,p,g) for i,(p,g) in enumerate(zip(P,G)) if not g < math.isqrt(p+1)]
print("records with g >= isqrt(p+1):", bad)
last=max(i for i,_,_ in bad)
print("from record index %d on (p >= %d) all records satisfy g < isqrt(p+1); records up to 2^64:"%(last+1,P[last]), sum(1 for p in P if p<2**64))
print("need direct check up to next record start p =", P[last], "<= N0:", P[last]<=N0)
