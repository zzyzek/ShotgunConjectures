# Brute-force A216971 from its definition for n<=6, compare to the
# closed formula T(n,k)=sum_r C(n,r) r! r^k C(m-1,k-1) m^(m-k), m=n-r,
# and compare the formula with the OEIS b-file; check n | T(n,k).
#
import itertools, math, sys
def rec(f):
  n=len(f); R=set()
  for x in range(n):
    y=f[x]
    for _ in range(n):
      if y==x: R.add(x); break
      y=f[y]
  return R
def brute(n):
  row=[0]*n
  for f in itertools.product(range(n),repeat=n):
    R=rec(f); k=sum(1 for x in range(n) if x not in R and f[x] in R); row[k]+=1
  return row
def formula(n,k):
  if k==0: return math.factorial(n)
  s=0
  for r in range(1,n+1):
    m=n-r
    if m<k: continue
    s+=math.comb(n,r)*math.factorial(r)*r**k*math.comb(m-1,k-1)*m**(m-k)
  return s
for n in range(1,7):
  b=brute(n); fo=[formula(n,k) for k in range(n)]
  assert b==fo,(n,b,fo)
vals=[int(l.split()[1]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
i=0;n=1
while i+n<=len(vals):
  row=vals[i:i+n]; assert row==[formula(n,k) for k in range(n)],n
  assert all(v%n==0 for v in row),n
  i+=n;n+=1
print("brute n<=6 ok; b-file rows 1..",n-1,"match formula, all divisible")
