# E4.4 Birch: can every 8 points in the plane (general position) be split into two triangles
# and a segment such that the segment meets the interior of both triangles?
import itertools, sys, numpy as np
def orient(a,b,c): return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def seg_hits_tri_interior(p,q,t):
    a,b,c=t
    s=1 if orient(a,b,c)>0 else -1
    inside=lambda x: s*orient(a,b,x)>0 and s*orient(b,c,x)>0 and s*orient(c,a,x)>0
    if inside(p) or inside(q): return True
    # segment crosses an edge properly -> enters interior (general position)
    cnt=0
    for u,v in ((a,b),(b,c),(c,a)):
        if orient(p,q,u)*orient(p,q,v)<0 and orient(u,v,p)*orient(u,v,q)<0: cnt+=1
    return cnt>=1
def ok(P):
    idx=range(8)
    for s in itertools.combinations(idx,2):
        rest=[i for i in idx if i not in s]
        for A in itertools.combinations(rest,3):
            if rest[0] not in A: continue
            B=[i for i in rest if i not in A]
            if seg_hits_tri_interior(P[s[0]],P[s[1]],[P[i] for i in A]) and seg_hits_tri_interior(P[s[0]],P[s[1]],[P[i] for i in B]):
                return True
    return False
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2]); bad=0
for it in range(N):
    m=it%3
    if m==0: P=rng.random((8,2))
    elif m==1:  # points near convex position
        th=np.sort(rng.random(8))*2*np.pi; r=1+0.05*rng.standard_normal(8); P=np.c_[r*np.cos(th),r*np.sin(th)]
    else:  # clustered / skewed
        P=rng.standard_normal((8,2))*np.array([1,rng.random()*0.3+0.01])+ (rng.random((8,1))<0.5)*rng.standard_normal(2)*3
    if not ok(P):
        bad+=1; print("COUNTEREXAMPLE?",P.tolist()); break
print("tested",it+1,"bad",bad)
