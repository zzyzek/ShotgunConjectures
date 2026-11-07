# Moebius polynomials M(n,x) = 1 + x*sum_{m<n} floor(n/m) M(m,x) (A074586).
# Checks: (1) M(n) = (1+x)M(n-1) + x*sum_{d|n,d<n} M(d) for 2<=n<=N;
# (2) ratio M(n,1) / (A077596(n)*sqrt(pi n/2)) and max-coefficient version.
import math
N=400
M=[None,[1]]
def add(a,b):
  r=[0]*max(len(a),len(b))
  for i,x in enumerate(a): r[i]+=x
  for i,x in enumerate(b): r[i]+=x
  return r
for n in range(2,N+1):
  s=[0]
  for m in range(1,n): s=add(s,[(n//m)*c for c in M[m]])
  M.append(add([1],[0]+s))
for n in range(2,N+1):
  e=[0]
  for d in range(1,n):
    if n%d==0: e=add(e,M[d])
  r=add(add(M[n-1],[0]+M[n-1]),[0]+e)
  assert r==M[n] or r+[0]*0==M[n], n
print("identity ok n<=",N)
for n in [50,100,200,300,400]:
  k0=(n-1)//2 if n%2 else n//2-1
  tot=sum(M[n]); c=M[n][k0]; mx=max(M[n])
  print(n, tot/(c*math.sqrt(math.pi*n/2)), tot/(mx*math.sqrt(math.pi*n/2)), mx==c)
