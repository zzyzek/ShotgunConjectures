# Check of the reduction: A = E_N/(F,G), N = n+1 even, F,G random quadrics, z random linear form (mod P).
# h_s = homology of z on A in degree s; predicted h_s = a(n,s+1) + a(n,s) - a(n+1,s+1).
import sys, itertools, random, numpy as np
exec(open('../../froberg-R/certificate/hs.py').read().split('def HS')[0].replace('def LN','def _LN'))
exec(open('apaths.py').read().split('for n in range')[0])
random.seed(5)
def elem(deg,N): return [(m,random.randrange(1,P)) for m in monos(N,deg)]
def mulmat(N,f,i,d):
    src=monos(N,i); dst=monos(N,i+d); idx={m:j for j,m in enumerate(dst)}
    M=np.zeros((len(src),len(dst)),dtype=np.int64)
    for a,m in enumerate(src):
        for fm,c in f:
            if m&fm: continue
            M[a,idx[m|fm]]=(M[a,idx[m|fm]]+c*sign(m,fm))%P
    return M
def Ibasis(N,F,G,s):
    if s<2: return np.zeros((0,C(N,s)),dtype=np.int64)
    return np.vstack([mulmat(N,F,s-2,2),mulmat(N,G,s-2,2)])
n=int(sys.argv[1]); N=n+1
F=elem(2,N); G=elem(2,N); z=elem(1,N)
for s in range(0,N):
    I_s=Ibasis(N,F,G,s); I_s1=Ibasis(N,F,G,s+1)
    dimI_s=rank(I_s) if len(I_s) else 0; dimI_s1=rank(I_s1) if len(I_s1) else 0
    Zs=mulmat(N,z,s,1)
    pre=C(N,s)-(rank(np.vstack([Zs,I_s1]))-dimI_s1)
    im=rank(np.vstack([mulmat(N,z,s-1,1),I_s])) if s>=1 else dimI_s
    h=pre-im
    pred=a(n,s+1)+a(n,s)-a(n+1,s+1)
    print(n,s,'h',h,'pred',pred,flush=True)
