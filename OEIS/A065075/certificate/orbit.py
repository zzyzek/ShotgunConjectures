# Accelerated simulation of the orbit x -> x + s(x) from x = 1 (A004207 without its leading 1).
# rec(j, h, L): the orbit inside a block of numbers H*10^j + L (L < 10^j) where s(H) = h, entered at offset L.
# Returns (e, mask): the orbit leaves the block at (H*10^j) + 10^j + e, and mask has bit t set iff some visited
# point in the block has s(L) = t (so its digit sum is h + t).
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
def s(n): return sum(map(int,str(n)))
@lru_cache(maxsize=None)
def rec(j, h, L):
  if j==1:
    mask=0
    while L<10:
      mask|=1<<L
      L=L+h+L
    return L-10, mask
  P=10**(j-1)
  d, Lp = divmod(L, P)
  mask=0
  while d<10:
    e, m = rec(j-1, h+d, Lp)
    mask |= m<<d
    Lp = e
    d += 1
    while Lp>=P and d<10:
      d+=1; Lp-=P
  # leaving: offset relative to 10^j
  return (d-10)*P + Lp, mask
def check(D):
  e, mask = rec(D, 0, 1)
  vals=[t for t in range(9*D+1) if mask>>t&1]
  return vals
if __name__=="__main__":
  D=int(sys.argv[1])
  vals=set(check(D))
  # validate against brute force for small D
  if D<=7:
    x=1; bf=set()
    while x<10**D: bf.add(s(x)); x+=s(x)
    print("brute force agrees:", bf==vals)
  miss=[m for m in range(1,9*D+1) if m%3 and m not in vals]
  first_miss=miss[0] if miss else None
  print("D=%d: digit sums seen below 10^D: %d values; all m%%3!=0 up to %s present; first missing %s"%(D,len(vals), (first_miss-1) if first_miss else 9*D, first_miss))
