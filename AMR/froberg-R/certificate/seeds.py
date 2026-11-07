# Search cyclically invariant 0/1 forms f = sum over rotations of seed sets (Z/n acting on indices) that attain
# the Lundqvist-Nicklasson bound a. Degrees are checked middle-first with early abort.
import sys, itertools
exec(open('hs.py').read().split('def HS')[0])
def hsdeg(n,f,d,i):
    src=monos(n,i-d); dst=monos(n,i); idx={m:j for j,m in enumerate(dst)}
    M=np.zeros((len(src),len(dst)),dtype=np.int64)
    for a,m in enumerate(src):
        for fm,c in f:
            if m&fm: continue
            M[a,idx[m|fm]]=(M[a,idx[m|fm]]+c*sign(m,fm))%P
    return C(n,i)-rank(M)
def ok(n,d,f,a):
    order=sorted(range(d,n+1),key=lambda i:abs(2*i-(n+d)))
    for i in order:
        if hsdeg(n,f,d,i)!=a[i]: return False
    return True
def orbit(S,n):
    out={}
    for r in range(n):
        m=sum(1<<((s+r)%n) for s in S)
        out[m]=1
    return out
def canon(S,n):
    best=None
    for r in range(n):
        for sg in (1,-1):
            T=tuple(sorted(((sg*s+r)%n) for s in S))
            if best is None or T<best: best=T
    return best
n=int(sys.argv[1]); d=int(sys.argv[2]); a=LN(n,d)
seeds=sorted({canon((0,)+c,n) for c in itertools.combinations(range(1,n),d-1)})
print(n,d,'a=',a,'seeds',len(seeds),flush=True)
found=None
for S in seeds:
    f=list(orbit(S,n).items())
    if ok(n,d,f,a): found=('1 seed',S); break
if not found:
    for S,T in itertools.combinations(seeds,2):
        for sg in (1,-1):
            g=orbit(S,n)
            for m,c in orbit(T,n).items(): g[m]=(g.get(m,0)+sg*c)
            f=[(m,c) for m,c in g.items() if c]
            if ok(n,d,f,a): found=('2 seeds',S,T,sg); break
        if found: break
print(n,d,'FOUND' if found else 'none',found,flush=True)
