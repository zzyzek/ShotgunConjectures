# Check the n-2 queen placements of K. Williams, arXiv:2404.18237, proof of Thm 6 (Monsky),
# on the n x n torus, for every n <= NMAX with 3 | n or 4 | n.
import sys
def place(n):
  if n == 4:  return [(0,0),(1,2)]
  if n == 6:  return [(0,0),(1,3),(2,5),(3,2)]
  P=[]
  def add(lo,hi,f):
    for t in range(lo,hi+1): P.append((t, f(t)))
  if n % 12 in (3,9):
    m=(n-3)//6
    add(0,m-1,lambda t:2*t); add(m,3*m,lambda t:2*t+1)
    add(3*m+2,4*m+1,lambda t:2*t); add(4*m+3,6*m+2,lambda t:2*t-1)
  elif n % 12 == 4:
    m=(n-4)//12
    add(0,2*m-1,lambda t:3*t); add(2*m,5*m-1,lambda t:3*t+2); add(5*m+1,6*m+1,lambda t:3*t)
    add(6*m+2,9*m+1,lambda t:3*t+1); add(9*m+2,12*m+2,lambda t:3*t+3)
  elif n % 12 == 6:
    m=(n-6)//12
    add(0,2*m-1,lambda t:3*t); add(2*m,6*m+1,lambda t:3*t+1); add(6*m+2,6*m+2,lambda t:3*t)
    add(6*m+4,8*m+3,lambda t:3*t-3); add(8*m+5,12*m+5,lambda t:3*t-4)
  elif n % 12 == 8:
    m=(n+4)//12
    add(0,2*m-2,lambda t:3*t); add(2*m,5*m-3,lambda t:3*t-2); add(5*m-2,6*m-3,lambda t:3*t)
    add(6*m-2,9*m-5,lambda t:3*t-1); add(9*m-3,12*m-5,lambda t:3*t-3)
  elif n % 12 == 0:
    m=n//12
    if m == 1: return None
    add(0,3*m-2,lambda t:3*t); add(3*m-1,4*m-3,lambda t:3*t+3); add(4*m-1,6*m-2,lambda t:3*t+2)
    add(6*m-1,9*m-2,lambda t:3*t+1); add(9*m,10*m-1,lambda t:3*t-2); add(10*m,12*m-1,lambda t:3*t-1)
  return P
def ok(n,P):
  for key in (lambda p:p[0], lambda p:p[1], lambda p:p[0]+p[1], lambda p:p[1]-p[0]):
    if len({key(p)%n for p in P}) != len(P): return False
  return len(P) == n-2
NMAX=int(sys.argv[1]); bad=[]
for n in range(3,NMAX+1):
  if n%3 and n%4: continue
  P=place(n)
  if P is None: print("n =",n,"uses the figure (not encoded)"); continue
  if not ok(n,P): bad.append(n)
print("bad:",bad)
