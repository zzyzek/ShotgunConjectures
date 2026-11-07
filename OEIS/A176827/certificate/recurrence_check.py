from fractions import Fraction as F
def polmul(a,b,N):
  c=[F(0)]*(N+1)
  for i,x in enumerate(a):
    if x==0: continue
    for j,y in enumerate(b):
      if i+j>N: break
      c[i+j]+=x*y
  return c
def run(q,N):
  A=[F(1)]
  for M in range(N):
    # bf(m) for m=1..M+1 using A[0..m-1]
    def bf(m):
      g=A[:m]
      s=F(0)
      for n in range(1,m+1):
        sc=[g[i]*F(1,q**n)**i for i in range(len(g))]
        P=[F(1)]
        for _ in range(n): P=polmul(P,sc,m)
        c=P[m-n] if m-n<len(P) else 0
        s+=c/n
      return m*s
    nxt=sum(bf(j+1)*A[M-j] for j in range(M+1))/(M+1)
    A.append(nxt)
  return [A[n]*q**(n*(n-1)//2) for n in range(N+1)]
print([int(x) if x.denominator==1 else x for x in run(3,9)])
