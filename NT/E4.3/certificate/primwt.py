# max over primitive A in [1,x] of sum_{a in A}(x+1-a); conjecture x^2/6+O(x)
import networkx as nx, itertools, sys
def mwac(x):
    G=nx.DiGraph()
    W=0
    for a in range(1,x+1):
        w=x+1-a; W+=w
        G.add_edge('s',('L',a),capacity=w); G.add_edge(('R',a),'t',capacity=w)
        for b in range(2*a,x+1,a): G.add_edge(('L',a),('R',b))
    f,_=nx.maximum_flow(G,'s','t')
    return W-f
def brute(x):
    best=0
    for r in range(1,x+1):
        for S in itertools.combinations(range(1,x+1),r):
            if all(b%a for a in S for b in S if a<b):
                best=max(best,sum(x+1-a for a in S))
    return best
for x in range(1,13): assert mwac(x)==brute(x),x
print("brute ok")
for x in [60,120,240,480,960,1500]:
    m=mwac(x); print(x,m,m/x**2, (m-x*x/6)/x)
