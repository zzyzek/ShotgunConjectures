# d = n-4, n odd: B_f(alpha, beta) = coefficient of alpha^beta^f on E_2. For f the Hodge dual of
# eta = sum_S (max S - min S) e_S, B[P,Q] = sign(P,Q) * (max - min of P u Q) for disjoint pairs P, Q.
# Rank mod P; full rank mod P implies full rank over Q.
import itertools, numpy as np
P=1000003
def perm_sign(seq):
    s=1
    for a in range(len(seq)):
        for b in range(a+1,len(seq)):
            if seq[a]>seq[b]: s=-s
    return s
def M(n):
    pairs=list(itertools.combinations(range(n),2)); idx={p:t for t,p in enumerate(pairs)}
    A=np.zeros((len(pairs),len(pairs)),dtype=np.int64)
    for p in pairs:
        for q in pairs:
            if set(p)&set(q): continue
            S=sorted(p+q); A[idx[p],idx[q]]=perm_sign(p+q)*(S[3]-S[0])
    return A
def rankp(A):
    M_=A.copy()%P; r=0; rows,cols=M_.shape
    for c in range(cols):
        nz=np.nonzero(M_[r:,c])[0]
        if len(nz)==0: continue
        piv=r+nz[0]; M_[[r,piv]]=M_[[piv,r]]
        M_[r]=(M_[r]*pow(int(M_[r,c]),P-2,P))%P
        col=M_[:,c].copy(); col[r]=0; nzr=np.nonzero(col)[0]
        if len(nzr): M_[nzr]=(M_[nzr]-np.outer(col[nzr],M_[r]))%P
        r+=1
        if r==rows: break
    return r
for n in range(7,24,2):
    A=M(n); print(n,'rank',rankp(A),'of',A.shape[0],flush=True)
