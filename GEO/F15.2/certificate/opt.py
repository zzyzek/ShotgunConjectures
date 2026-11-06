import random, math, itertools, sys
n=int(sys.argv[1]); seed=int(sys.argv[2]) if len(sys.argv)>2 else 0
perms=[p for p in itertools.permutations(range(n)) if p[0]<p[-1]]
def L(P):
    return min(sum(math.dist(P[p[i]],P[p[i+1]]) for i in range(n-1)) for p in perms)
random.seed(seed); best=(0,None)
for rep in range(150):
    P=[(random.random(),random.random()) for _ in range(n)]; f=L(P); st=0.2
    for it in range(3000):
        Q=[(min(1,max(0,x+random.gauss(0,st))),min(1,max(0,y+random.gauss(0,st)))) for x,y in P]
        g=L(Q)
        if g>f: P,f=Q,g
        if it%300==299: st*=0.6
    if f>best[0]: best=(f,P)
print(n,best)
