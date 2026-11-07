# A088081(n) = least prime P such that for every r <= n two primes <= P differ by a multiple of r.
# g(r) = least prime P with two primes <= P congruent mod r; A088081(n) = max_{r<=n} g(r).
# A088082 = n with A088081(n+1) > A088081(n). Lists n with n+1 composite.
import sys
from sympy import primerange, isprime
M=int(sys.argv[1])
ps=list(primerange(2,10**6))
def g(r):
  seen=set()
  for p in ps:
    if p%r in seen: return p
    seen.add(p%r)
A=[None]+[0]*M; cur=0
for r in range(1,M+1):
  cur=max(cur,g(r)); A[r]=cur
print("A088081(1..20):",A[1:21])
B=[n for n in range(1,M) if A[n+1]>A[n]]
print("A088082 start:",B[:25])
print("n with n+1 composite:",[n for n in B if not isprime(n+1)][:40])
print("count",len(B),"composite",sum(1 for n in B if not isprime(n+1)))
