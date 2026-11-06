"""Exact solver for the Macaulay systems M s = v (drop-in for gen_lean.gp_solve).

1. numpy, mod p = 2^31 - 1: row echelon form of [M | v]. If v is a pivot column the system has no
   solution mod p and None is returned (a rational solution could in principle need p in a
   denominator; that only makes the exponent search pick a larger e, never an unsound result).
2. The pivot columns C and a set R of independent rows of M[:, C] (echelon form of the transpose)
   give a minor A = M[R, C] that is nonsingular mod p, hence over Q.
3. PARI/gp `matsolve(A, v_R)` (for integer matrices PARI uses p-adic lifting, no fraction-free
   elimination over Q); all other unknowns are 0.
The result is checked by gen_lean.solve_member (exact polynomial identity in sympy) and again
by the Lean kernel; nothing here is trusted.
Environment: RPI_GP_MEM (bytes, default 4e9) is the PARI stack cap.
"""
import os, sys, subprocess, tempfile
import numpy as np
from sympy import Rational, ilcm
import gen_lean

GP_MEM = int(float(os.environ.get('RPI_GP_MEM', '4e9')))
P = 2147483647
MODONLY = False


def echelon_pivots(A):
    """Pivot columns of the row echelon form of A (int64 array, entries in [0, P)), in place."""
    nr, nc = A.shape
    piv, r = [], 0
    for c in range(nc):
        if r == nr:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        k = r + nz[0]
        if k != r:
            A[[r, k]] = A[[k, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r, c:] = (A[r, c:] * inv) % P
        below = A[r+1:, c].copy()
        nzb = np.nonzero(below)[0]
        if len(nzb):
            rows = r + 1 + nzb
            A[rows, c:] = (A[rows, c:] - (below[nzb, None] * A[r, c:][None, :]) % P) % P
        piv.append(c)
        r += 1
    return piv


def gp_solve(nr, nc, entries, rhs):
    den = 1
    for _, _, co in entries:
        den = ilcm(den, Rational(co).q)
    for _, co in rhs:
        den = ilcm(den, Rational(co).q)
    Mi = {}
    for r, c, co in entries:
        Mi[(r, c)] = int(Rational(co) * den)
    vi = {r: int(Rational(co) * den) for r, co in rhs}
    A = np.zeros((nr, nc + 1), dtype=np.int64)
    for (r, c), x in Mi.items():
        A[r, c] = x % P
    for r, x in vi.items():
        A[r, nc] = x % P
    piv = echelon_pivots(A)
    del A
    if nc in piv:
        return None
    if MODONLY:
        return 'MODOK'
    C = piv
    B = np.zeros((len(C), nr), dtype=np.int64)
    cidx = {c: k for k, c in enumerate(C)}
    for (r, c), x in Mi.items():
        if c in cidx:
            B[cidx[c], r] = x % P
    R = echelon_pivots(B)
    del B
    assert len(R) == len(C)
    ridx = {r: k for k, r in enumerate(R)}
    n = len(C)
    lines = [f'default(nbthreads, 1); default(parisizemax, {GP_MEM});', f'A = matrix({n},{n});', f'w = vector({n})~;']
    for (r, c), x in Mi.items():
        if r in ridx and c in cidx:
            lines.append(f'A[{ridx[r]+1},{cidx[c]+1}] = {x};')
    for r, x in vi.items():
        if r in ridx:
            lines.append(f'w[{ridx[r]+1}] = {x};')
    lines.append('s = matsolve(A, w); for(i = 1, #s, print(s[i]));')
    with tempfile.NamedTemporaryFile('w', suffix='.gp', delete=False) as f:
        f.write('\n'.join(lines) + '\nquit;\n'); fn = f.name
    r = subprocess.run(['gp', '-q', '-D', 'recover=0', '-s', '100000000', fn], capture_output=True, text=True,
                       timeout=20000, stdin=subprocess.DEVNULL)
    out = r.stdout.strip()
    bad = [l for l in r.stderr.split('\n') if '***' in l and 'Warning' not in l]
    if bad or '***' in r.stdout or r.returncode != 0:
        raise RuntimeError('gp error: ' + r.stderr[-800:] + r.stdout[:300])
    os.unlink(fn)
    s = [Rational(x.strip()) for x in out.split('\n') if x.strip()]
    assert len(s) == n
    sol = [Rational(0)] * nc
    for k, c in enumerate(C):
        sol[c] = s[k]
    return sol


def install():
    gen_lean.gp_solve = gp_solve


def feasible(gens, gweights, V, weights, target, w):
    """True iff target is in the span mod p (necessary for a rational solution)."""
    global MODONLY
    from sympy import Poly, QQ
    cols = []
    for k, (g, gw) in enumerate(zip(gens, gweights)):
        if w - gw < 0:
            continue
        for m in gen_lean.wt_monos(weights, w - gw):
            mp = Poly(dict([(m, 1)]), *V, domain=QQ)
            cols.append((mp*g).as_dict())
    rows = gen_lean.wt_monos(weights, w)
    ridx = {r: i for i, r in enumerate(rows)}
    if not cols:
        return False
    old, MODONLY = MODONLY, True
    try:
        r = gp_solve(len(rows), len(cols), [(ridx[mon], c, co) for c, dct in enumerate(cols) for mon, co in dct.items()],
                     [(ridx[mon], co) for mon, co in target.as_dict().items()])
    finally:
        MODONLY = old
    return r == 'MODOK'
