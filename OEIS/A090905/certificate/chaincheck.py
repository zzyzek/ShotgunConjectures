# Bertrand chain b: 2,3,5,7,13,23,... (A006992: largest prime < 2*prev).
# For consecutive (r,q,p) check: p > 5q/3, q < 2r, and the exact
# integrality v_l((2p)!) + v_l((2r)!) >= 2 v_l((2q)!) for all primes l
# (done exactly while q <= 10^4), plus the "q > 72" threshold of the proof.
def isprime(m):
  if m < 2: return False
  i = 2
  while i*i <= m:
    if m % i == 0: return False
    i += 1
  return True
def leg(n,l):
  s=0; x=l
  while x<=n: s+=n//x; x*=l
  return s
b=[2]
while b[-1] < 10**12:
  m=2*b[-1]-1
  while not isprime(m): m-=1
  b.append(m)
print("chain", b[:12])
for i in range(len(b)-2):
  r,q,p=b[i],b[i+1],b[i+2]
  ok = 3*p > 5*q
  integ = None
  if q <= 10**4:
    integ = all(leg(2*p,l)+leg(2*r,l) >= 2*leg(2*q,l) for l in range(2,2*p+1) if isprime(l))
  print(r,q,p, "p>5q/3:",ok, "integral:",integ, "q>72:", q>72)
