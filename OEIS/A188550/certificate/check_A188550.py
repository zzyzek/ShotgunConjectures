# A188550: a(n) = max_{2<=k<=isqrt(n)} #{d>1 : d | n-k, k | n-d}.
# Test Shevelev's conjecture: max over 2<=k<=(n-2)//2 is the same for n >= 6.
import sys, math
N = int(sys.argv[1])
divs = [[] for _ in range(N+1)]
for d in range(2, N+1):
  for m in range(d, N+1, d): divs[m].append(d)
def f(n,k): return sum(1 for d in divs[n-k] if (n-d) % k == 0)
bad = 0
for n in range(4, N+1):
  s = math.isqrt(n)
  a = max(f(n,k) for k in range(2, s+1))
  hi = max([f(n,k) for k in range(s+1, (n-2)//2+1)] or [0])
  if n >= 6 and hi > a:
    bad += 1
    if bad < 30: print("counterexample n", n, "a", a, "max over large k", hi, [k for k in range(s+1,(n-2)//2+1) if f(n,k)==hi][:5])
print("N", N, "bad", bad)
