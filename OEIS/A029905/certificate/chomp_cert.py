# Certify that row r=120 of 3-row Chomp has neither a P-position (q,q,120)
# nor a one-parameter family (k+P+Q, k+Q, 120), k>=0.
# f(q,r) (q>=r): unique p with (p,min(p,q),min(p,q,r)) a P-position.
import sys
from functools import lru_cache
R = int(sys.argv[1]); QMAX = int(sys.argv[2])

# --- brute-force game check of the recurrence on small boards
def brute(N):
    P = {}
    pos = [(p,q,r) for p in range(1,N+1) for q in range(0,p+1) for r in range(0,q+1)]
    pos.sort(key=sum)
    for (p,q,r) in pos:
        moves = set()
        for a in range(1,p): moves.add((a,min(q,a),min(r,a)))
        for a in range(0,q): moves.add((p,a,min(r,a)))
        for a in range(0,r): moves.add((p,q,a))
        P[(p,q,r)] = not any(P[m] for m in moves)
    return P

def table(R, QMAX):
    f = {}
    for q in range(0, QMAX+1):
        for r in range(0, min(q,R)+1):
            # diagonal hit p' < q in chain: (p',p',min(p',r)) P
            hit = None
            for pp in range(1, q):
                if f[(pp, min(pp,r))] == pp: hit = pp; break
            if hit is not None: f[(q,r)] = hit; continue
            E = set(f[(a, min(r,a))] for a in range(q)) | set(f[(q,b)] for b in range(r))
            p = max(q,1)
            while p in E: p += 1
            f[(q,r)] = p
    return f

N = 14
B = brute(N); fs = table(N, N)
for q in range(N+1):
    for r in range(q+1):
        Ps = [p for p in range(max(q,1),N+1) if B[(p,q,r)]]
        Pd = [p for p in range(1,q) if B[(p,p,min(p,r))]]
        allp = Ps + Pd
        if fs[(q,r)] <= N: assert allp == [fs[(q,r)]] or sorted(allp)==[fs[(q,r)]], (q,r,allp,fs[(q,r)])
print("recurrence matches brute force for boards up to", N)
