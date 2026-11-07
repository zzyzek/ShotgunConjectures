# s(m,n): least s such that every n-colouring of [m, m+s] has a monochromatic x+y=z (x=y allowed).
import sys
from pysat.solvers import Solver
def var(i,c,m,n): return (i-m)*n+c+1
def solve(m,n,s,want_model=False):
  N=m+s; S=Solver(name='cadical153')
  for i in range(m,N+1): S.add_clause([var(i,c,m,n) for c in range(n)])
  for x in range(m,N+1):
    for y in range(x,N+1):
      z=x+y
      if z>N: break
      for c in range(n):
        S.add_clause(list({-var(x,c,m,n),-var(y,c,m,n),-var(z,c,m,n)}))
  # symmetry: m gets colour 0
  S.add_clause([var(m,0,m,n)])
  r=S.solve(); mod=S.get_model() if (r and want_model) else None; S.delete(); return r,mod
def smn(m,n,lo):
  s=lo
  while solve(m,n,s)[0]: s+=1
  return s
n=int(sys.argv[1])
for m in range(1,int(sys.argv[2])+1):
  lo={2:4*m-2,3:13*m-3,4:40*m-2}.get(n,1)
  print(m, smn(m,n,lo), flush=True)
