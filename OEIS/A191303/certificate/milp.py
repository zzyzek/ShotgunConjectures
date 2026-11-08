# Search b = al*t + be, c = b + d, digits a_i t + e_i (i = 1..k, base-b most significant first)
# with m(t) = sum m_i b^(k-i) = sum m_i c^(i-1) identically, valid for all t >= 1.
import sys, numpy as np
from math import comb
from scipy.optimize import milp, LinearConstraint, Bounds
from fractions import Fraction
def polymul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i + j] += x * y
    return r
def ppow(p, e):
    r = [1]
    for _ in range(e): r = polymul(r, p)
    return r
def eqs(k, al, be, d):
    b = [be, al]; c = [be + d, al]
    rows = [[0] * (2 * k) for _ in range(k + 1)]
    for i in range(1, k + 1):
        w = [0] * (k + 1)
        for j, x in enumerate(ppow(b, k - i)): w[j] += x
        for j, x in enumerate(ppow(c, i - 1)): w[j] -= x
        for p in range(k + 1):
            if p + 1 <= k: rows[p + 1][2 * (i - 1)] += w[p]
            rows[p][2 * (i - 1) + 1] += w[p]
    return rows
def check(k, al, be, d, x):
    a = x[0::2]; e = x[1::2]
    for t in range(1, k + 3):
        b = al * t + be; c = b + d
        m = [a[i] * t + e[i] for i in range(k)]
        if b < 2 or any(v < 0 or v >= b for v in m) or m[0] == 0 or m[-1] == 0: return False
        if sum(m[i] * b**(k - 1 - i) for i in range(k)) != sum(m[i] * c**i for i in range(k)): return False
    return all(0 <= a[i] <= al for i in range(k)) and a[0] >= 1
def solve(k, al, be, d, E=10**6):
    A = np.array(eqs(k, al, be, d), dtype=float)
    n = 2 * k
    cons = [LinearConstraint(A, 0, 0)]
    G = []; lo = []; hi = []
    for i in range(k):
        r = [0] * n; r[2*i] = 1; r[2*i+1] = 1; G.append(r); lo.append(0); hi.append(al + be - 1)  # t=1 digit range
    r = [0]*n; r[0] = 1; r[1] = 1; G.append(r); lo.append(1); hi.append(np.inf)
    r = [0]*n; r[2*k-2] = 1; r[2*k-1] = 1; G.append(r); lo.append(1); hi.append(np.inf)
    cons.append(LinearConstraint(np.array(G, dtype=float), lo, hi))
    lb = []; ub = []
    for i in range(k):
        lb += [1 if i == 0 else 0, -E]; ub += [al, E]
    res = milp(c=np.zeros(n), constraints=cons, integrality=np.ones(n), bounds=Bounds(lb, ub))
    if res.status == 0:
        x = [int(round(v)) for v in res.x]
        return x if check(k, al, be, d, x) else None
    return None
if __name__ == '__main__':
    k = int(sys.argv[1]); AL = int(sys.argv[2])
    for al in range(1, AL + 1):
        for d in range(1, al + 3):
            for be in range(max(2 - al, -al), al + 1):
                x = solve(k, al, be, d)
                if x:
                    print(k, al, be, d, x, flush=True); sys.exit()
    print('none', k, AL)
