# Check: (i) the limit of the insertion process (simulated to depth 60, prefix
# stabilised) against the b-file; (ii) the block formula a(4j+i) = A_j + i d_j,
# (A_0,d_0) = (0,1), (A,d) -> (A+4d, A+5d); (iii) the six section claims.
#
import sys, math
def step(s):
  out=[s[0]]
  for i in range(len(s)-1):
    a,b=s[i],s[i+1]
    if 4*b<=5*a: out.append(a+b)
    out.append(b)
  return out
b=[int(l.split()[1]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
s=[1,1]
for k in range(60): s=step(s)
s2=step(s)
m=0
while s[m]==s2[m]: m+=1
print("stable prefix length at depth 60:",m)
assert s[:min(m,len(b))]==b[:min(m,len(b))]
A,d=0,1; f=[]
while len(f)<len(b):
  f+= [A+i*d for i in range(1,5)]; A,d=A+4*d,A+5*d
assert f[:len(b)]==b; print("block formula = b-file, n=1..",len(b))
a=lambda n: f[n-1]
def rec(x0,x1,N):
  r=[x0,x1]
  while len(r)<N: r.append(6*r[-1]-r[-2])
  return r
N=240
issq=lambda v: v>=0 and math.isqrt(v)**2==v
sol1=[x for x in range(1,a(2*N+1)+1) if issq(2*x*x+7)] if False else None
# (1) a(2n+1): every term satisfies 2x^2+7 square, and up to 10^7 the
#     solutions are exactly these terms
sec1=[a(2*n+1) for n in range(N)]
assert all(issq(2*x*x+7) for x in sec1)
S1=set(x for x in range(0,10**7) if issq(2*x*x+7)); assert S1==set(x for x in sec1 if x<10**7)
assert rec(1,9,N)==[a(4*n+1) for n in range(N)]
sec3=[a(4*n+2) for n in range(N)]
assert all(issq((k*k+4)//2) and k%2==0 for k in sec3)
S3=set(k for k in range(0,10**7) if (k*k+4)%2==0 and issq((k*k+4)//2)); assert S3==set(x for x in sec3 if x<10**7)
assert rec(1,7,N)==[a(4*n+2)//2 for n in range(N)] and all(a(4*n+2)%2==0 for n in range(N))
assert rec(0,4,N+1)[1:]==[a(4*n+4) for n in range(N)]
assert rec(0,1,N+1)[1:]==[a(4*n+4)//4 for n in range(N)] and all(a(4*n+4)%4==0 for n in range(N))
print("six section claims hold for n <",N,"; solution sets match below 10^7")
