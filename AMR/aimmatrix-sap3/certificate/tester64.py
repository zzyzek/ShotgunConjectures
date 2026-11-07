# Read enum output for (n, m); for each k report: patterns passing the exact two-term condition
# (k coefficients with >= 2 monomials), how many also have generic Jacobian rank k, and whether
# the beta-nilpotent-Jacobian sufficient test succeeds.
import sys, itertools, subprocess, numpy as np
rng = np.random.default_rng(7)
n=int(sys.argv[1]); m=int(sys.argv[2]); ks=[int(a) for a in sys.argv[3].split(',')]
lines=subprocess.run(['./enum64',str(n),str(m),str(min(ks))],capture_output=True,text=True).stdout.split('\n')
pats=[]
for L in lines:
    if not L.strip(): continue
    f=L.split(); w=int(f[0]); t=[int(z) for z in f[1:]]
    P=[(b//n,b%n) for b in range(n*n) if (w>>b)&1]
    pats.append((P,t))
def alpha(P,x):
    A=np.zeros((n,n))
    for ij,v in zip(P,x): A[ij]=v
    return np.poly(A)[1:].real
def jac(P,x):
    a0=alpha(P,x); J=np.zeros((n,len(P)))
    for t in range(len(P)):
        y=x.copy(); y[t]+=1.0; J[:,t]=alpha(P,y)-a0
    return J
def genrank(P,b):
    r=0
    for _ in range(3):
        x=rng.normal(size=len(P)); r=max(r,np.linalg.matrix_rank(jac(P,x)[b],tol=1e-8))
    return r
def nj(P,b,tries=15):
    for _ in range(tries):
        x=rng.normal(size=len(P))
        for it in range(80):
            r=alpha(P,x)[b]
            if np.max(np.abs(r))<1e-12: break
            x=x+np.linalg.lstsq(jac(P,x)[b],-r,rcond=None)[0]
            if np.max(np.abs(x))>1e6: break
        r=alpha(P,x)[b]
        if np.max(np.abs(r))<1e-9 and np.min(np.abs(x))>1e-3*max(1,np.max(np.abs(x))):
            s=np.linalg.svd(jac(P,x)[b],compute_uv=False)
            if s[-1]>1e-6*max(1,s[0]): return x
    return None
for k in ks:
    two=0; gr=0; ok=None
    for P,t in pats:
        T=[i for i in range(1,n+1) if t[i-1]>=2]
        if len(T)<k: continue
        two+=1; anygr=False
        for beta in itertools.combinations(T,k):
            b=[i-1 for i in beta]
            if genrank(P,b)<k: continue
            anygr=True
            if ok is None:
                x=nj(P,b)
                if x is not None: ok=(beta,P,np.round(x,4).tolist())
        gr+=anygr
    print(f"n={n} m={m} k={k}: two-term {two}, +generic rank {gr}, NJ-success {ok}",flush=True)
