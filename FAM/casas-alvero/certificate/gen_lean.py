"""Emit the Lean core lemma and degree-d theorem for Casas-Alvero in degree d.

Core lemma (variables b_1..b_{d-2}, x_1..x_{d-2} in a char-0 field):
  Q(x) = x^d + sum_{j=1}^{d-2} b_j x^j,  H_i = Q^{(i)}/i!.
  Hypotheses Q(x_i) = 0, H_i(x_i) = 0 (i = 1..d-2).  Conclusion b_j = 0 for all j.
Stage 1: R_i(b) = Res_x(Q, H_i) = U_i(x_i) Q(x_i) + V_i(x_i) H_i(x_i)   (cofactors by linear algebra).
Stage 2: N_j b_j^{e_j} = sum_i g_ij R_i                                  (cofactors by linear algebra).
Every identity is re-checked here with sympy before it is printed, and again by `ring` in Lean.
"""
import sys
from sympy import symbols, Poly, diff, factorial, expand, QQ, resultant, lcm, binomial, sympify
from sympy.polys.matrices import DomainMatrix

def wt_monos(weights, w):
    out = []
    def rec(k, rem, cur):
        if k == len(weights):
            if rem == 0: out.append(tuple(cur))
            return
        for e in range(rem // weights[k] + 1):
            rec(k+1, rem - e*weights[k], cur+[e])
    rec(0, w, [])
    return out

def solve_member(gens, gweights, V, weights, target, w):
    """target (Poly, weighted-homogeneous of weight w) = sum cof_k gens_k; returns (den, cofs) with
    den*target = sum cofs_k gens_k (integer coefficients), or None."""
    cols, info = [], []
    for k, (g, gw) in enumerate(zip(gens, gweights)):
        if w - gw < 0: continue
        for m in wt_monos(weights, w - gw):
            mp = Poly(dict([(m, 1)]), *V, domain=QQ)
            cols.append((mp*g).as_dict()); info.append((k, m))
    rows = wt_monos(weights, w)
    ridx = {r: i for i, r in enumerate(rows)}
    nr, nc = len(rows), len(cols)
    if nc == 0: return None
    sol = gp_solve(nr, nc, [(ridx[mon], c, co) for c, dct in enumerate(cols) for mon, co in dct.items()],
                   [(ridx[mon], co) for mon, co in target.as_dict().items()])
    if sol is None: return None
    den = 1
    for s in sol: den = lcm(den, s.q)
    cof = [dict() for _ in gens]
    for c, s in enumerate(sol):
        if s != 0:
            k, m = info[c]; cof[k][m] = s*den
    cofp = [Poly(cf, *V, domain=QQ) if cf else Poly(0, *V, domain=QQ) for cf in cof]
    lhs = sum((cp*g for cp, g in zip(cofp, gens)), Poly(0, *V, domain=QQ))
    assert lhs == target*den
    return den, cofp

def gp_solve(nr, nc, entries, rhs):
    """Solve M s = v over QQ with PARI/gp (matinverseimage); None if no solution."""
    import subprocess, tempfile, os
    from sympy import Rational
    lines = ['default(nbthreads, 1); default(parisizemax, 1600000000);', f'M = matrix({nr},{nc});', f'v = vector({nr})~;']
    for r, c, co in entries:
        lines.append(f'M[{r+1},{c+1}] = {co};')
    for r, co in rhs:
        lines.append(f'v[{r+1}] = {co};')
    lines.append('p = 1000000007; sp = matinverseimage(M * Mod(1, p), v * Mod(1, p));')
    lines.append('if(#sp == 0, print("NONE"), s = matinverseimage(M, v); if(#s == 0, print("NONE"), for(i = 1, #s, print(s[i]))));')
    with tempfile.NamedTemporaryFile('w', suffix='.gp', delete=False) as f:
        f.write('\n'.join(lines) + '\nquit;\n'); fn = f.name
    r = subprocess.run(['gp', '-q', '-D', 'recover=0', '-s', '100000000', fn], capture_output=True, text=True,
                       timeout=3000, stdin=subprocess.DEVNULL)
    out = r.stdout.strip()
    # gp exits 0 after an error unless recover=0; check the code and both streams.
    #
    if (r.returncode != 0) or ('***' in r.stderr) or ('***' in r.stdout):
        raise RuntimeError('gp error: ' + r.stderr[:500] + r.stdout[:500])
    if out.startswith('NONE'):
        os.unlink(fn); return None
    sol = [Rational(x.strip()) for x in out.split('\n') if x.strip()]
    if len(sol) != nc:
        open(fn + '.out', 'w').write(out); raise RuntimeError('parse ' + fn)
    return sol

def lean(e):
    s = str(e.as_expr() if isinstance(e, Poly) else e)
    return s.replace('**', '^')

def core(d, maxe=80):
    b = list(symbols(' '.join(f'b{j}' for j in range(1, d-1)), seq=True))
    xs = list(symbols(' '.join(f'x{i}' for i in range(1, d-1)), seq=True))
    t = symbols('t')
    Qt = t**d + sum(b[j-1]*t**j for j in range(1, d-1))
    Ht = [expand(diff(Qt, t, i)/factorial(i)) for i in range(1, d-1)]
    out = []
    name = f'core{d}'
    hyps = []
    for i in range(1, d-1):
        x = xs[i-1]
        hyps.append(f'(hQ{i} : {lean(expand(Qt.subs(t, x)))} = 0)')
        hyps.append(f'(hH{i} : {lean(expand(Ht[i-1].subs(t, x)))} = 0)')
    vars_ = ' '.join(map(str, b + xs))
    concl = ' ∧ '.join(f'{v} = 0' for v in b)
    out.append(f'theorem {name} {{K : Type*}} [Field K] [CharZero K] ({vars_} : K)\n    ' +
               '\n    '.join(hyps) + f' :\n    {concl} := by')
    # stage 1
    R = []
    for i in range(1, d-1):
        x = xs[i-1]
        V1 = b + [x]
        W1 = [d - j for j in range(1, d-1)] + [1]
        Qx = Poly(Qt.subs(t, x), *V1, domain=QQ); Hx = Poly(Ht[i-1].subs(t, x), *V1, domain=QQ)
        Ri = Poly(resultant(Qt, Ht[i-1], t), *b, domain=QQ)
        res = solve_member([Qx, Hx], [d, d-i], V1, W1, Poly(Ri.as_expr(), *V1, domain=QQ), d*(d-i))
        assert res is not None, ('stage1', i)
        den, (U, Vv) = res
        R.append(Ri)
        out.append(f'  have r{i} : ({den}:K) * ({lean(Ri)}) = 0 := by\n'
                   f'    linear_combination ({lean(U)}) * hQ{i} + ({lean(Vv)}) * hH{i}')
    # stage 2: use den*R_i as generators (r_i says den_i*R_i = 0, so R_i = 0 needs den != 0); simpler:
    for i in range(len(R)):
        out.append(f'  have s{i+1} : ({lean(R[i])}) = 0 := (mul_eq_zero.mp r{i+1}).resolve_left (by norm_num)')
    W = [d - j for j in range(1, d-1)]
    GW = [d*(d-i) for i in range(1, d-1)]
    stats = []
    for j in range(len(b)):
        for e in range(1, maxe+1):
            tgt = Poly(b[j]**e, *b, domain=QQ)
            res = solve_member(R, GW, b, W, tgt, e*W[j])
            if res is not None: break
        assert res is not None, ('stage2', j)
        den, cofs = res
        stats.append((j+1, e, len(str(den)), [len(c.terms()) for c in cofs]))
        comb = ' + '.join(f'({lean(c)}) * s{k+1}' for k, c in enumerate(cofs) if not c.is_zero)
        out.append(f'  have t{j+1} : ({den}:K) * b{j+1}^{e} = 0 := by\n    linear_combination {comb}')
        out.append(f'  have z{j+1} : b{j+1} = 0 := pow_eq_zero_iff (n := {e}) (by norm_num) |>.mp\n'
                   f'    ((mul_eq_zero.mp t{j+1}).resolve_left (by norm_num))')
    out.append('  exact ' + (f'z1' if len(b) == 1 else '⟨' + ', '.join(f'z{j+1}' for j in range(len(b))) + '⟩'))
    return '\n'.join(out), stats

if __name__ == '__main__':
    d = int(sys.argv[1])
    txt, stats = core(d)
    print(txt)
    print('-- stats', stats, file=sys.stderr)
