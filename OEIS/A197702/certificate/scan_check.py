# Brute-force a(n) by subset sums of odd numbers; compare with the conjectured rule.
#
import math
N=20000; best={}
S={0}
for k in range(1,200):
  S=S|{s+2*k-1 for s in S}
  T=k*k
  for s in S:
    n=T-2*s
    if 0<n<=N and n not in best: best[n]=k
def rule(n):
  k=math.isqrt(n-1)+1
  d=k*k-n
  return k if d==0 else (k+2 if d==4 else (k+1 if d%2 else k))
print(all(best[n]==rule(n) for n in range(1,N+1)))
