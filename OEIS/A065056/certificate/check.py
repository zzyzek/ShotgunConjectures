# Recaman R(n) (A005132) and partial sums S(n) = A065056(n); prints S(n)/n^2 and min 4S(n)/(n(n+1)).
import sys
N=int(sys.argv[1]); seen=bytearray(8*N); a=0; S=0; seen[0]=1; worst=9
for n in range(1,N+1):
  b=a-n
  if b>=0 and not seen[b]: a=b
  else: a=a+n
  if a>=len(seen): seen.extend(bytearray(a-len(seen)+N))
  seen[a]=1; S+=a
  worst=min(worst,4*S/(n*(n+1)))
  if n in (10**3,10**4,10**5,10**6,10**7): print(n,S,S/n**2,"min 4S/(n(n+1)) so far",worst)
