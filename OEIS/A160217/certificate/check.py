def v2(x):
  c=0
  while x%2==0: x//=2; c+=1
  return c
chi=lambda x: v2(x)%2==0
def nxt(x,c):
  y=x+1
  while chi(y)!=c: y+=1
  return y
def a(n): return 2*n+1 if v2(n)%2==0 else 2*n+2
worst=(0,0); viol=0
for m in range(4,3000):
  if not chi(m): continue
  b=m; n=1; prev=b-a(1)
  while b!=a(n):
    n+=1; b=nxt(b,chi(n))
    d=b-a(n)
    if d>prev: viol+=1
    prev=d
  worst=max(worst,(n,m))
print("worst merge (n,m)",worst,"increases of b-a:",viol)
bad=0;ex=None
for n in range(1,3000):
  for x in range(a(n)+1,a(n)+200):
    if chi(x)==chi(n) and nxt(x,chi(n+1))-x > a(n+1)-a(n):
      bad+=1; ex=ex or (n,x,a(n),a(n+1),nxt(x,chi(n+1)))
print("pointwise violations",bad,ex)
