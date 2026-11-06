import itertools, sys
from brute import ok
def model(g,n):
    for j in range(2):
        col=[g[i][j] for i in range(n)]
        blocks=[c for k,c in enumerate(col) if k==0 or col[k-1]!=c]
        if len(set(blocks))!=len(blocks): return False
    for c in range(1,5):
        L=[i for i in range(n) if g[i][0]==c]; R=[i for i in range(n) if g[i][1]==c]
        if L and R:
            sh=[i for i in L if i in R]
            if not sh: return False
            for i in sh:
                if i not in (L[0],L[-1]) or i not in (R[0],R[-1]): return False
    return True
rows=list(itertools.product(range(1,5),repeat=2))
for n in range(2,int(sys.argv[1])+1):
    bad=0;cnt=0
    for mid in itertools.product(rows,repeat=n-2):
        g=[(1,2)]+list(mid)+[(3,4)]
        a=ok(g,n); b=model(g,n)
        if a!=b: bad+=1
        cnt+=a
    print(n,cnt,"mismatch",bad,flush=True)
