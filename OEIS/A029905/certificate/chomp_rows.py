# Classify rows r <= R of 3-row Chomp: finite (P-position (q,q,r) exists,
# q > r) or infinite with a certified eventually periodic offset f(q,r)-q.
# Certificate: finite-state induction on S_q = {v-q : v used in row r, v>=q}.
import sys
R = int(sys.argv[1]); QMAX = int(sys.argv[2])
f = {}
used = [set() for _ in range(R+1)]
hit = [None]*(R+1)
for q in range(0, QMAX+1):
    for r in range(0, min(q,R)+1):
        if hit[r] is not None:
            f[(q,r)] = hit[r]
        else:
            col = set(f[(q,b)] for b in range(r))
            p = max(q,1)
            while (p in used[r]) or (p in col): p += 1
            f[(q,r)] = p
    # update used sets / hits with column q (a = q contributes f(q,min(r,q)))
    for r in range(0, R+1):
        v = f[(q, min(r,q))]
        used[r].add(v)
        if hit[r] is None and q >= 1 and v == q: hit[r] = q
# certify rows
info = {}
for r in range(R+1):
    if hit[r] is not None:
        info[r] = ('finite', hit[r]); continue
    q0 = max([r+1] + [info[b][1] for b in range(r) if info[b][0]=='inf'] +
             [info[b][1]+1 for b in range(r) if info[b][0]=='finite'])
    assert q0 <= QMAX - 50, (r, q0)
    def D(q):
        s = set()
        for b in range(r):
            if info[b][0]=='finite':
                assert info[b][1] < q
            else:
                _, st, per, offs = info[b]
                assert q >= st
                s.add(offs[(q-st) % per])
        return s
    L = 1
    for b in range(r):
        if info[b][0]=='inf': L = L*info[b][2]//__import__('math').gcd(L, info[b][2])
    usedq0 = set(f[(a, min(r,a))] for a in range(q0))
    S = frozenset(v-q0 for v in usedq0 if v >= q0)
    seen = {}; offs = []; q = q0
    while True:
        key = ((q-q0) % L, S)
        if key in seen: break
        seen[key] = q
        Dq = D(q); t = 0
        while t in S or t in Dq: t += 1
        assert t >= 1, ('row becomes finite at', r, q)
        if q <= QMAX: assert f[(q,r)] == q+t, (r,q)
        offs.append(t)
        S = frozenset(s-1 for s in (S | {t}) if s >= 1)
        q += 1
        assert q < q0 + 100000
    q1 = seen[key]; per = q - q1
    cyc = offs[q1-q0:]
    for qq in range(r+1, q1):
        assert f[(qq,r)] != qq
    info[r] = ('inf', q1, per, cyc)
fin = [r for r in range(R+1) if info[r][0]=='finite']
lin = [r for r in range(R+1) if info[r][0]=='inf' and len(set(info[r][3]))==1]
oth = [r for r in range(R+1) if info[r][0]=='inf' and len(set(info[r][3]))>1]
print("h (finite rows, r>=1):", [r for r in fin if r>=1][:30], "count", len(fin))
print("r (linear families):", lin[:25], "count", len(lin))
print("neither:", [(r, info[r][1], info[r][2], info[r][3]) for r in oth])
