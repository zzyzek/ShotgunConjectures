# The 66 reflection/doubling/tripling relations on the 36 block-residue sums imply the identities (sympy rank test; prints certificate sizes).
from sympy import Matrix, Rational, zeros
def idx(j,r): return 6*j+r
def system(e2,e3,mm=1):
    rows=[]
    def row(): return [0]*36
    for j in range(6):
        for r in range(6):
            R=row(); R[idx(5-j,(mm-r)%6)]+=1; R[idx(j,r)]+=1; rows.append(R)
    for j in range(6):
        t=j//3
        for r in range(3):
            R=row(); R[idx(j,r)]+=e2; R[idx(j,r+3)]+=e2
            s=(2*r-t*mm)%6
            R[idx(2*j-6*t,s)]-=1; R[idx(2*j+1-6*t,s)]-=1; rows.append(R)
    for j in range(6):
        t=j//2
        for r in range(2):
            R=row()
            for q in (r,r+2,r+4): R[idx(j,q)]+=e3
            s=(3*r-t*mm)%6
            for i in range(3): R[idx(3*j-6*t+i,s)]-=1
            rows.append(R)
    return Matrix(rows)
def functional(coefs):
    # coefs: dict interval-> coefficient on s_j (sum over all residues)
    f=[0]*36
    for j,c in coefs.items():
        for r in range(6): f[idx(j,r)]+=c
    return Matrix([f])
for (name,e2,e3,targets) in [("7 mod 24",1,-1,{"h3-2h6":{0:-1,1:1},"h6-h2":{1:-1,2:-1}}),
                              ("19 mod 24",-1,-1,{"h2+3h6":{0:4,1:1,2:1},"h3+2h6":{0:3,1:1}})]:
    A=system(e2,e3)
    rk=A.rank()
    print(name,"rank",rk,"of 36")
    for tn,c in targets.items():
        f=functional(c)
        print("  ",tn,"implied:",A.col_join(f).rank()==rk)

print("---- certificates")
for (name,e2,e3,targets) in [("7 mod 24",1,-1,{"h3-2h6":{0:-1,1:1},"h6-h2":{1:-1,2:-1}}),
                              ("19 mod 24",-1,-1,{"h2+3h6":{0:4,1:1,2:1},"h3+2h6":{0:3,1:1}})]:
    A=system(e2,e3)
    for tn,c in targets.items():
        f=functional(c)
        sol,params=A.T.gauss_jordan_solve(f.T)
        sol=sol.subs({p:0 for p in params})
        nz=[(i,sol[i]) for i in range(len(sol)) if sol[i]!=0]
        print(name,tn,len(nz),"relations used")
