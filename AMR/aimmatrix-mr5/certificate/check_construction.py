# Re-derivation of the upper bound mr(complement of KG(n,k)) <= n-2k+2 (Hu-Tang 2026, s=1 case):
# nodes t_1..t_n, q_S(x) = prod_{i not in S} (x - t_i), A[S,T] = sum_i w_i q_S(t_i) q_T(t_i),
# w_i = 1/prod_{j!=i}(t_i - t_j) (order n-1 divided difference of q_S q_T).
# Checks exactly over Q: off-diagonal zero pattern = disjointness, and rank = n-2k+2.
import itertools, random, sys
from fractions import Fraction as F
import sympy
def run(n,k,seed):
    random.seed(seed)
    t=random.sample(range(-50,50),n)
    w=[F(1,1) for _ in range(n)]
    for i in range(n):
        d=1
        for j in range(n):
            if j!=i: d*=(t[i]-t[j])
        w[i]=F(1,d)
    subs=list(itertools.combinations(range(n),k))
    def q(S,x):
        r=1
        for i in range(n):
            if i not in S: r*=(x-t[i])
        return r
    A=[[sum(w[i]*q(S,t[i])*q(T,t[i]) for i in range(n)) for T in subs] for S in subs]
    for a,S in enumerate(subs):
        for b,T in enumerate(subs):
            if a!=b and ((A[a][b]==0) != (len(set(S)&set(T))==0)): return ('pattern fail',S,T)
    r=sympy.Matrix(A).rank()
    return r
for (n,k) in [(5,2),(6,2),(7,3),(8,3),(8,4),(9,3),(9,4),(10,4)]:
    print(n,k,'rank',run(n,k,1),'target',n-2*k+2,flush=True)
