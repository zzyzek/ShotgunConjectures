# Coefficients of the g.f. by power-series division (exact integers),
# then 6-sections against +-Fibonacci / Lucas.
#
def mul(p,q):
  r=[0]*(len(p)+len(q)-1)
  for i,u in enumerate(p):
    for j,v in enumerate(q): r[i+j]+=u*v
  return r
num=[1]
for f in ([1,-1],[1,1],[1,1],[1,0,1],[1,0,-1,2,1]): num=mul(num,f)
den=mul([1,0,-1,0,-1],[1,0,1,0,2,0,-1,0,1])
N=600; a=[]
for n in range(N):
  s=(num[n] if n<len(num) else 0)-sum(den[i]*a[n-i] for i in range(1,min(n,len(den)-1)+1))
  a.append(s)
F=[0,1]
for i in range(800): F.append(F[-1]+F[-2])
L=[2,1]
for i in range(800): L.append(L[-1]+L[-2])
for r in range(6): print(r,a[r::6][:6])
Fs=set(F)
nn=set(v for v in a if v>=0); not2=set(a[n] for n in range(N) if n%6!=2)
print("nonneg terms all Fib:",nn<=Fs," n!=2 mod 6 terms all Fib:",not2<=Fs," nonneg==not2:",nn==not2)
print("Fib indices missing up to 290:",[i for i in range(291) if F[i] not in nn])
print("a(6n+2) = -L(3n+1):",all(a[6*n+2]==-L[3*n+1] for n in range(N//6)))
