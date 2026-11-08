# For q=5: every n = 2^a 3^b prod_{p in E} p^e (a>=1,b>=1, exponent bounds from moves.py) with n > LIM
# admits m > n with phi(m) < phi(n). Moves: m = n/d * 5 * r, d a divisor made of <=2 prime powers of n, r>=1.
import itertools, sys
from sympy import factorint
LIM=int(sys.argv[1])
bnd={2:5,3:2,7:2,11:2,13:1,17:2,19:2,23:2,29:1,37:2,41:2,43:2,67:2}
P=sorted(bnd)
fcache={}
def fac(r):
    if r not in fcache: fcache[r]=factorint(r)
    return fcache[r]
def phi_of(f):
    x=1
    for p,e in f.items():
        if e>0: x*=(p-1)*p**(e-1)
    return x
def move(f,n,ph):
    items=[(p,i) for p,e in f.items() for i in range(1,e+1)]
    ds=[{p:i} for p,i in items]+[{p:i,p2:i2} for (p,i),(p2,i2) in itertools.combinations(items,2) if p!=p2]
    for dd in ds:
        d=1
        for p,i in dd.items(): d*=p**i
        g=dict(f)
        for p,i in dd.items(): g[p]-=i
        g[5]=g.get(5,0)+1
        lo=d//5+1
        for r in range(lo, lo*2+10):
            h=dict(g)
            for p,e in fac(r).items(): h[p]=h.get(p,0)+e
            if phi_of(h)<ph: return (dd,r)
    return None
cnt=0;bad=[]
for ex in itertools.product(*[range(1 if p in (2,3) else 0, bnd[p]+1) for p in P]):
    n=1
    for p,e in zip(P,ex): n*=p**e
    if n<=LIM: continue
    f={p:e for p,e in zip(P,ex) if e}
    cnt+=1
    if move(f,n,phi_of(f)) is None: bad.append(n)
print("candidates >",LIM,":",cnt,"without move:",len(bad),bad[:20])
