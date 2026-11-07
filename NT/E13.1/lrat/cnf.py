# As e13gen.py plus colour-symmetry breaking: m -> 0, 2m -> 1, and colour 3 at i needs colour 2 at some j < i.
# opt amo=1 adds at-most-one clauses.
import sys
m,n,s=map(int,sys.argv[1:4]); amo=len(sys.argv)>4 and sys.argv[4]=="1"; N=m+s
v=lambda i,c:(i-m)*n+c+1
cl=[]
for i in range(m,N+1): cl.append([v(i,c) for c in range(n)])
for x in range(m,N+1):
  for y in range(x,N+1):
    if x+y>N: break
    for c in range(n):
      cl.append([-v(x,c),-v(y,c),-v(x+y,c)] if x!=y else [-v(x,c),-v(x+y,c)])
if amo:
  for i in range(m,N+1):
    for a in range(n):
      for b in range(a+1,n): cl.append([-v(i,a),-v(i,b)])
cl.append([v(m,0)]); cl.append([v(2*m,1)])
for i in range(m+1,N+1): cl.append([-v(i,3)]+[v(j,2) for j in range(m,i)])
print("p cnf %d %d"%((N-m+1)*n,len(cl)))
for c in cl: print(" ".join(map(str,c)),0)
