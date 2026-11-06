import sys
from collections import Counter
def a(n): return n*(2*n*n+6*n-5)//3
def cnt(n):
  # number of (x,w,y,z) in [1,n]^4 with x*w - y*z = 2n
  P = Counter(x*w for x in range(1,n+1) for w in range(1,n+1))
  return sum(c*P.get(v+2*n,0) for v,c in P.items())
N = int(sys.argv[1])
bad = []
for n in range(3, N+1):
  c, t = cnt(n), a(n-2)
  if c != t: bad.append((n, c, t))
print("first mismatches:", bad[:10], "count", len(bad))
