# Problem R: Hilbert series of E/(f), f odd degree d in the exterior algebra on n generators, mod a prime P,
# compared with the Lundqvist-Nicklasson lower bound a = b + c (Cor. 3.2). Since rank over Q >= rank mod P and
# HS(E/(f)) >=_lex a over Q for every odd form, HS mod P = a implies HS over Q = a for that integer form.
import sys, itertools, numpy as np
from math import comb
P = 1000003
def C(n,k): return comb(n,k) if 0<=k<=n else 0
def LN(n,d):
    b=[]
    for i in range(n+1):
        if 2*i <= n+d: b.append(sum((-1)**k*C(n,i-k*d) for k in range(0,i//d+1)))
        else: b.append(sum((-1)**(k+1)*C(n,i+k*d) for k in range(1,n+1) if i+k*d<=n))
    a=b[:]
    if (n-d)%2==0 and ((n-d)//2)%2==1 and b[(n-d)//2]%2==1: a[(n+d)//2]+=1
    return a
def sign(a,b):
    s=0; bb=b
    while bb:
        y=bb&-bb; s+=bin(a&~((y<<1)-1)).count("1"); bb^=y
    return -1 if s&1 else 1
def monos(n,k): return [sum(1<<j for j in c) for c in itertools.combinations(range(n),k)]
def rank(M):
    M=M.copy()%P; r=0; rows,cols=M.shape
    for c in range(cols):
        nz=np.nonzero(M[r:,c])[0]
        if len(nz)==0: continue
        piv=r+nz[0]; M[[r,piv]]=M[[piv,r]]
        M[r]=(M[r]*pow(int(M[r,c]),P-2,P))%P
        col=M[:,c].copy(); col[r]=0; nzr=np.nonzero(col)[0]
        if len(nzr): M[nzr]=(M[nzr]-np.outer(col[nzr],M[r]))%P
        r+=1
        if r==rows: break
    return r
def HS(n,f,d):
    h=[]
    for i in range(n+1):
        if i<d: h.append(C(n,i)); continue
        src=monos(n,i-d); dst=monos(n,i); idx={m:j for j,m in enumerate(dst)}
        M=np.zeros((len(src),len(dst)),dtype=np.int64)
        for a,m in enumerate(src):
            for fm,c in f:
                if m&fm: continue
                M[a,idx[m|fm]]=(M[a,idx[m|fm]]+c*sign(m,fm))%P
        h.append(C(n,i)-rank(M))
    return h
