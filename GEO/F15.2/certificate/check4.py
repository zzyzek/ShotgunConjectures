# Numerical sanity check of the n = 4 argument: for random triangles in [0,1]^2 with a point D inside,
# the averaged bound (2P + b)/3 dominates the shortest Hamiltonian path, and it never exceeds (4+3*sqrt2)/3.
import random, math, itertools
random.seed(7)
perms=[p for p in itertools.permutations(range(4)) if p[0]<p[-1]]
def L(P): return min(sum(math.dist(P[p[i]],P[p[i+1]]) for i in range(3)) for p in perms)
worst=0; viol=0
for t in range(200000):
    A,B,C=[(random.random(),random.random()) for _ in range(3)]
    u,v=random.random(),random.random()
    if u+v>1: u,v=1-u,1-v
    D=(A[0]+u*(B[0]-A[0])+v*(C[0]-A[0]),A[1]+u*(B[1]-A[1])+v*(C[1]-A[1]))
    s=sorted([math.dist(B,C),math.dist(C,A),math.dist(A,B)]); P=sum(s)
    bound=(2*P+s[1])/3
    if L([A,B,C,D])>bound+1e-12: viol+=1
    worst=max(worst,bound)
print("violations",viol,"max bound",worst,"(4+3sqrt2)/3 =",(4+3*math.sqrt(2))/3)
