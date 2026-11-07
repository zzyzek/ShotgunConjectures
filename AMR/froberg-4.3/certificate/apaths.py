from math import comb
def C(n,k): return comb(n,k) if 0<=k<=n else 0
def a(n,s):
    if s==0: return 1
    if n-2*s+2<1: return 0
    d=n-2*s+4
    return sum(C(n,s-k*d)-2*C(n,s-2-k*d)+C(n,s-4-k*d) for k in range(0,s//max(d,1)+2))
def paths(n,s):
    W=n+2-2*s
    if W<1: return 0 if s>0 else 1
    cur={0:1}
    for j in range(n+2):
        nxt={}
        for x,c in cur.items():
            for y in (x+1,x-1):
                if 0<=y<=W: nxt[y]=nxt.get(y,0)+c
        cur=nxt
    return cur.get(W,0)
for n in range(3,24):
    assert all(a(n,s)==paths(n,s) for s in range(1,n//2+1)), n
for n in range(3,24,2):
    lb=[a(n+1,s)-a(n,s-1) for s in range(1,n//2+2)]
    ok=[s for s in range(1,n//2+2) if lb[s-1]>=a(n,s)]
    print(n,[a(n,s) for s in range(n//2+2)], 'zbound ok s:',ok, 'known <=',n//3+1)
