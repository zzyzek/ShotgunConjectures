import sys
# Minimal runlength code (A227368) by L* + greedy lex with exact feasibility.
# String from the top: runs r_1..r_k (1s,0s,1s,...), sum r = L,
# partition sum N = sum_t t*r_t - k(k-1)/2.
def lstar(N):
  best=None
  m=1
  while m<=N:
    k=-(-N//m)
    v=m+k-1
    if best is None or v<best: best=v
    m+=1
  return best
def feasible(t,U,S,N,L):
  R=L-U
  if R==0: return (t>=1 and S-t*(t-1)//2==N)
  for j in range(1,R+1):
    T=N+(t+j)*(t+j-1)//2-S
    base=sum(range(t+1,t+j+1))
    lo=base+(t+1)*(R-j); hi=base+(t+j)*(R-j)
    if lo<=T<=hi: return True
  return False
def code(N):
  if N==0: return [], 0
  L=lstar(N)
  runs=[];U=0;S=0;t=0
  while U<L:
    rng=range(1,L-U+1)
    order = rng if (t%2==0) else reversed(rng)
    for r in order:
      if feasible(t+1,U+r,S+(t+1)*r,N,L):
        runs.append(r);U+=r;S+=(t+1)*r;t+=1;break
    else: raise Exception("no")
  assert feasible(t,U,S,N,L)
  return runs,L
def tonum(runs):
  s='';b='1'
  for r in runs: s+=b*r; b='0' if b=='1' else '1'
  return int(s,2) if s else 0
def parts(runs):
  # from top: p_k = ..., differences r_t-1 for t<k, last run = smallest part
  if not runs: return []
  k=len(runs); p=[runs[-1]]
  for r in reversed(runs[:-1]): p.append(p[-1]+r-1)
  return p  # ascending
def a761(N):
  if N<2: return 0
  p=parts(code(N)[0])
  return max([p[i+1]-p[i] for i in range(len(p)-1)]+[0])
if __name__=="__main__":
  M=int(sys.argv[1])
  for N in range(M+1):
    runs,L=code(N)
    print(N,tonum(runs),a761(N),parts(runs))
