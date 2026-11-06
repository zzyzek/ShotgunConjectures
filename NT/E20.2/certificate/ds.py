# N_d(n): max length of a sequence on n letters, no immediate repetition, no alternation
# a..b..a.. of length > d. State: seen letters ordered by last occurrence (oldest first) and
# the alternation length of every pair; appending the letter of rank i raises the pair count
# with every more recent letter by one.
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
d=int(sys.argv[1]); n=int(sys.argv[2])
@lru_cache(maxsize=None)
def f(k, M):
  # M: tuple of rows; M[i][j-i-1] = count of pair (i,j), i<j, ranks by recency
  best=0
  if k<n:
    if d>=2 or k==0:
      newM=tuple(tuple(list(r)+[2]) for r in M)+((),)
      best=max(best,1+f(k+1,newM))
  for i in range(k-1):
    row=M[i]
    if any(c+1>d for c in row): continue
    # build new matrix: letters order: all except i, then i at top
    cnt={}
    for a in range(k):
      for b in range(a+1,k):
        c=M[a][b-a-1]
        if a==i: c+=1
        cnt[(a,b)]=c
    order=[a for a in range(k) if a!=i]+[i]
    pos={a:p for p,a in enumerate(order)}
    rows=[]
    for p in range(k):
      a=order[p]; r=[]
      for q in range(p+1,k):
        b=order[q]; r.append(cnt[(min(a,b),max(a,b))])
      rows.append(tuple(r))
    best=max(best,1+f(k,tuple(rows)))
  return best
print(d,n,f(0,()), f.cache_info().currsize)
