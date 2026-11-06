# Brute force: least m >= 1 with exactly n even divisors (n <= 18), via a divisor-count sieve
# up to 2^18 (even divisors of 2y correspond to divisors of y); compare with the data and 2^n.
N=2**18
d=[0]*(N+1)
for i in range(1,N+1):
  for j in range(i,N+1,i): d[j]+=1
data=[1,2,4,8,12,32,24,128,48,72,96,2048,120,8192,384,288,240,131072,360]
best={}
for m in range(1,N+1):
  e = d[m//2] if m%2==0 else 0
  if e not in best: best[e]=m
a=[best[n] for n in range(19)]
assert a==data, a
isprime=lambda n: n>1 and all(n%q for q in range(2,n))
for n in range(1,19): assert (a[n]==2**n)==(isprime(n) or n==1)
print("ok; a(0) =",a[0],"= 2^0")
