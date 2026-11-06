import sys
# Closed-form route: valid pairs (m,k), m+k-1=L*, D=mk-N; greedy deltas per pair; lex compare.
def lstar(N):
  return min(m + (-(-N//m)) - 1 for m in range(1, N+1))
def runs_for(m,k,D):
  R=D; d=[]
  for t in range(1,k):
    if t==k-1: x=R
    elif t%2==1: x=0
    else: x=R//(k-t)
    d.append(x); R-=(k-t)*x
  assert R==0
  return [x+1 for x in d]+[m-sum(d)]
def key(r):
  return [ (x if i%2==0 else -x) for i,x in enumerate(r)]
def best(N):
  L=lstar(N); cands=[]
  for m in range(1,L+1):
    k=L+1-m
    if m*k>=N: cands.append((key(runs_for(m,k,m*k-N)),m,k,m*k-N,runs_for(m,k,m*k-N)))
  return min(cands), L
if __name__=="__main__":
  M=int(sys.argv[1])
  for N in range(2,M+1):
    (kk,m,k,D,r),L=best(N)
    print(N,m,k,D,max([x-1 for x in r[:-1]]+[0]),r)
