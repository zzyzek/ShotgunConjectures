from math import comb
N=40
f=[]
for n in range(N):
  f.append(1-sum(comb(n,i)*f[i] for i in range(n) if (n-i)%2==0))
print(f[:10])
# coefficients of F^m
def mul(p,q): return [sum(p[i]*q[k-i] for i in range(k+1)) for k in range(N)]
Fp=[[1]+[0]*(N-1)]
for m in range(1,N): Fp.append(mul(Fp[-1],f))
a=[]
for n in range(N):
  a.append(f[n]-sum(a[m]*Fp[m][n-m] for m in range(n)))
print(a[:16])
data=[1,1,-1,0,3,0,-38,0,947,0,-37394,0,2120190,0,-162980012,0,16330173251,0,-2070201641498,0,324240251016266,0,-61525045423103316,0,13913915097436287598,0,-3698477457114061621492,0]
assert a[:len(data)]==data
for m in range(N):
  assert (a[m]%2==1) == (m==0 or (m&(m-1))==0)
print("ok")
