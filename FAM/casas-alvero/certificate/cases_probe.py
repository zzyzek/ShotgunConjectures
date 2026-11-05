"""Probe: certificate sizes for the case split R_i = b_i^m S_i (b_i = 0 or S_i = 0)."""
import sys, itertools, time
from sympy import symbols, Poly, diff, factorial, expand, resultant, factor_list, QQ
import gen_lean
d = int(sys.argv[1])
t = symbols('t'); b = list(symbols(' '.join(f'b{j}' for j in range(1, d-1)), seq=True))
W = [d - j for j in range(1, d-1)]
Q = t**d + sum(b[j-1]*t**j for j in range(1, d-1))
S = []
for i in range(1, d-1):
    H = expand(diff(Q, t, i)/factorial(i)); R = resultant(Q, H, t)
    fl = [f for f, m in factor_list(R)[1] if Poly(f, *b).total_degree() > 1 or len(Poly(f, *b).terms()) > 1]
    assert len(fl) == 1
    S.append(Poly(fl[0], *b, domain=QQ))
SW = [sum(e*w for e, w in zip(s.monoms()[0], W)) for s in S]
tot = 0; mx = 0
for T in itertools.product([0, 1], repeat=d-2):
    gens = [Poly(b[i], *b, domain=QQ) if T[i] else S[i] for i in range(d-2)]
    gw = [W[i] if T[i] else SW[i] for i in range(d-2)]
    for j in range(d-2):
        if T[j]: continue
        for e in range(1, 80):
            r = gen_lean.solve_member(gens, gw, b, W, Poly(b[j]**e, *b, domain=QQ), e*W[j])
            if r: break
        den, cof = r
        sz = len(str(den)) + sum(len(str(c.as_expr())) for c in cof)
        tot += sz; mx = max(mx, sz)
        print(T, j+1, 'e', e, 'den digits', len(str(den)), 'chars', sz, flush=True)
print('total chars', tot, 'max', mx)
