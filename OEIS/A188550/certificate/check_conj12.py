# Shevelev's 2013 conjectures 1), 2) for A188550: a(p)=1 only for p=5,7,13; a(p)=2 only for p=11,19.
import sys, math
N = int(sys.argv[1])
divs = [[] for _ in range(N+1)]
for d in range(2, N+1):
  for m in range(d, N+1, d): divs[m].append(d)
sieve = bytearray([1])*(N+1); sieve[0]=sieve[1]=0
for i in range(2,int(N**.5)+1):
  if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
def f(n,k): return sum(1 for d in divs[n-k] if (n-d) % k == 0)
one=[];two=[]
for p in range(5,N+1):
  if not sieve[p]: continue
  a = max(f(p,k) for k in range(2, math.isqrt(p)+1))
  if a==1: one.append(p)
  if a==2: two.append(p)
print("N",N,"a(p)=1:",one,"a(p)=2:",two)
