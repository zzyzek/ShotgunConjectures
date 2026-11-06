"""Core lemma core<d> for Casas-Alvero with reflective (RPI.check, `decide +kernel`) certificates.

Same mathematics as gen_lean.core (split=False) and gen_cases.core_cases (split=True):
Stage 1 (per i): den_i * b_i^m_i * S_i(b) = U Q(x_i) + V H_i(x_i), with Res_x(Q, H_i) = c b_i^m_i S_i
(split=False: m_i = 0 and S_i = Res_x(Q, H_i)).
Stage 2 (per case T, per j not in T): den * b_j^e = sum_{i in T} g_i b_i + sum_{i not in T} g_i S_i.
The cofactors go into `def` constants (RPI.Poly literals); each identity is one `decide +kernel`
call on RPI.check. The statement of core<d> is the same as in gen_lean / gen_cases, so
gen_degree.section can use it unchanged.
"""
import itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sympy import symbols, Poly, diff, factorial, expand, resultant, factor_list, QQ, ZZ, Rational
import gen_lean
from gen_lean import lean

SOLVER = gen_lean.solve_member
CACHE = os.environ.get('RPI_CACHE')
FEAS = None


def solve(gens, gw, V, W, tgt, w):
    """SOLVER with an optional on-disk cache (RPI_CACHE=dir); results are re-verified anyway."""
    if not CACHE:
        return SOLVER(gens, gw, V, W, tgt, w)
    import hashlib, pickle
    key = hashlib.sha256(repr(([sorted(g.as_dict().items()) for g in gens], gw, [str(v) for v in V], W, sorted(tgt.as_dict().items()), w)).encode()).hexdigest()
    fn = os.path.join(CACHE, key + '.pkl')
    if os.path.exists(fn):
        return pickle.load(open(fn, 'rb'))
    r = SOLVER(gens, gw, V, W, tgt, w)
    os.makedirs(CACHE, exist_ok=True)
    pickle.dump(r, open(fn, 'wb'))
    return r


def lit(p, nv):
    """RPI.Poly literal of an integer polynomial (Poly or dict), terms sorted ascending lex."""
    dct = p.as_dict() if isinstance(p, Poly) else p
    terms = []
    for m, c in sorted(dct.items()):
        if c == 0:
            continue
        assert len(m) == nv, (m, nv)
        c = Rational(c)
        assert c.q == 1, 'non-integer coefficient'
        c = int(c.p)
        terms.append(f'([{",".join(map(str, m))}], {c})')
    return '[' + ', '.join(terms) + ']'


def plit(p, nv):
    """Packed literal for the rpi% elaborator (large data: cofactors and S_i)."""
    dct = p.as_dict() if isinstance(p, Poly) else p
    out = []
    for m, c in sorted(dct.items()):
        c = Rational(c)
        if c == 0:
            continue
        assert c.q == 1 and len(m) == nv
        out.append(','.join(map(str, m)) + ':' + str(int(c.p)))
    return 'rpi% "' + ';'.join(out) + '"'


def mono(nv, k, e):
    return '[' + ','.join(str(e if i == k else 0) for i in range(nv)) + ']'


def core_reflect(d, split, maxe=80, log=sys.stderr):
    t = symbols('t')
    nb = d - 2
    b = list(symbols(' '.join(f'b{j}' for j in range(1, d-1)), seq=True))
    xs = list(symbols(' '.join(f'x{i}' for i in range(1, d-1)), seq=True))
    W = [d - j for j in range(1, d-1)]
    Qt = t**d + sum(b[j-1]*t**j for j in range(1, d-1))
    Ht = [expand(diff(Qt, t, i)/factorial(i)) for i in range(1, d-1)]
    bs = ' '.join(map(str, b))
    bl = '[' + ', '.join(map(str, b)) + ']'
    out, S, M, SW, hypQ, hypH = [], [], [], [], [], []
    stats = []
    for i in range(1, nb+1):
        x = xs[i-1]
        R = resultant(Qt, Ht[i-1], t)
        if split:
            fl = factor_list(R)[1]
            m = [mm for f, mm in fl if f == b[i-1]][0]
            Sf = [f for f, mm in fl if f != b[i-1]]
            assert len(Sf) == 1
            Si = Poly(Sf[0], *b, domain=ZZ)
        else:
            m, Si = 0, Poly(R, *b, domain=ZZ)
        S.append(Si); M.append(m)
        SW.append(sum(e*w for e, w in zip(Si.monoms()[0], W)))
        V1 = b + [x]; W1 = W + [1]
        Qx = Poly(Qt.subs(t, x), *V1, domain=QQ); Hx = Poly(Ht[i-1].subs(t, x), *V1, domain=QQ)
        tgt = Poly(b[i-1]**m * Si.as_expr(), *V1, domain=QQ)
        r = solve([Qx, Hx], [d, d-i], V1, W1, tgt, d*(d-i))
        assert r, ('stage1', i)
        den, (U, Vv) = r
        stats.append(('r', i, m, len(str(den))))
        hq = lean(expand(Qt.subs(t, x))); hh = lean(expand(Ht[i-1].subs(t, x)))
        hypQ.append(hq); hypH.append(hh)
        n1 = nb + 1
        out.append(f'def S{d}_{i} : RPI.Poly := {plit(Si, nb)}\n')
        out.append(f'def Q{d}_{i} : RPI.Poly := {lit(Qx, n1)}\n')
        out.append(f'def H{d}_{i} : RPI.Poly := {lit(Hx, n1)}\n')
        out.append(f'def U{d}_{i} : RPI.Poly := {plit(U, n1)}\n')
        out.append(f'def V{d}_{i} : RPI.Poly := {plit(Vv, n1)}\n')
        out.append(
            f'theorem core{d}_r{i} {{K : Type*}} [Field K] ({bs} {x} : K)\n'
            f'    (hQ : {hq} = 0) (hH : {hh} = 0) :\n'
            f'    ({den}:K) * ({b[i-1]}^{m} * RPI.Poly.eval {bl} S{d}_{i}) = 0 := by\n'
            f'  have hk := RPI.check_zero [{", ".join(map(str, b))}, {x}] (fs := [Q{d}_{i}, H{d}_{i}])\n'
            f'    (gs := [U{d}_{i}, V{d}_{i}]) (t := RPI.mul [({mono(n1, i-1, m)}, {den})] S{d}_{i})\n'
            f'    (by decide +kernel) (by\n'
            f'      intro f hf\n'
            f'      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf\n'
            f'      rcases hf with rfl | rfl\n'
            f'      · simp only [Q{d}_{i}, RPI.Poly.eval, RPI.Mono.eval]; push_cast; linear_combination hQ\n'
            f'      · simp only [H{d}_{i}, RPI.Poly.eval, RPI.Mono.eval]; push_cast; linear_combination hH)\n'
            f'  have ea := RPI.Poly.eval_append {bl} [{x}] (n := {nb}) rfl S{d}_{i} (by decide +kernel)\n'
            f'  simp only [List.cons_append, List.nil_append] at ea\n'
            f'  rw [RPI.mul_eval, ea] at hk\n'
            f'  simp only [RPI.Poly.eval, RPI.Mono.eval] at hk\n'
            f'  push_cast at hk\n'
            f'  linear_combination hk\n')
    masks = [T for T in itertools.product([0, 1], repeat=nb) if not all(T)] if split else [tuple([0]*nb)]
    for T in masks:
        tag = ''.join(map(str, T))
        gens = [Poly(b[i], *b, domain=QQ) if T[i] else Poly(S[i].as_expr(), *b, domain=QQ) for i in range(nb)]
        gw = [W[i] if T[i] else SW[i] for i in range(nb)]
        hyps = ' '.join(f'(h{i+1} : {b[i]} = 0)' if T[i] else f'(h{i+1} : RPI.Poly.eval {bl} S{d}_{i+1} = 0)'
                        for i in range(nb))
        fsl = ', '.join(f'[({mono(nb, i, 1)}, 1)]' if T[i] else f'S{d}_{i+1}' for i in range(nb))
        zl = []
        for j in range(nb):
            if T[j]:
                continue
            if FEAS:
                # b_j^e in the ideal (with these weight bounds) is monotone in e: binary search
                # mod p, then one exact solve.
                ok = lambda e: FEAS(gens, gw, b, W, Poly(b[j]**e, *b, domain=QQ), e*W[j])
                lo, hi = 0, 8
                while not ok(hi):
                    lo, hi = hi, 2*hi
                    assert hi <= 4*maxe, (T, j)
                while hi - lo > 1:
                    mid = (lo + hi)//2
                    if ok(mid):
                        hi = mid
                    else:
                        lo = mid
                e = hi
                r = solve(gens, gw, b, W, Poly(b[j]**e, *b, domain=QQ), e*W[j])
            else:
                for e in range(1, maxe+1):
                    r = solve(gens, gw, b, W, Poly(b[j]**e, *b, domain=QQ), e*W[j])
                    if r:
                        break
            assert r, (T, j)
            den, cof = r
            stats.append((tag, j+1, e, len(str(den))))
            nm = f'G{d}_{tag}_{j+1}'
            for k, c in enumerate(cof):
                out.append(f'def {nm}_{k+1} : RPI.Poly := {plit(c, nb)}\n')
            gsl = ', '.join(f'{nm}_{k+1}' for k in range(nb))
            alts = ' | '.join(['rfl'] * nb)
            cases = []
            for i in range(nb):
                if T[i]:
                    cases.append(f'      · simp only [RPI.Poly.eval, RPI.Mono.eval]\n'
                                 f'        simp [h{i+1}]')
                else:
                    cases.append(f'      · exact h{i+1}')
            fh = (f'      intro f hf\n'
                  f'      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf\n'
                  f'      rcases hf with {alts}\n' + '\n'.join(cases)) if nb > 1 else \
                 (f'      intro f hf\n      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf\n'
                  f'      subst hf\n' + cases[0].replace('      · ', '      ', 1))
            out.append(
                f'theorem core{d}_c{tag}_{j+1} {{K : Type*}} [Field K] ({bs} : K)\n'
                f'    {hyps} :\n    ({den}:K) * {b[j]}^{e} = 0 := by\n'
                f'  have hk := RPI.check_zero {bl} (fs := [{fsl}]) (gs := [{gsl}])\n'
                f'    (t := [({mono(nb, j, e)}, {den})]) (by decide +kernel) (by\n{fh})\n'
                f'  simp only [RPI.Poly.eval, RPI.Mono.eval] at hk\n'
                f'  push_cast at hk\n'
                f'  linear_combination hk\n')
            zl.append((j, e))
        if split:
            lines = [f'theorem core{d}_case{tag} {{K : Type*}} [Field K] [CharZero K] ({bs} : K)\n'
                     f'    {hyps} :\n    ' + ' ∧ '.join(f'{v} = 0' for v in b) + ' := by']
            hs = ' '.join(f'h{i+1}' for i in range(nb))
            for j, e in zl:
                lines.append(f'  have z{j+1} : {b[j]} = 0 := pow_eq_zero_iff (n := {e}) (by norm_num) |>.mp\n'
                             f'    ((mul_eq_zero.mp (core{d}_c{tag}_{j+1} {bs} {hs})).resolve_left (by norm_num))')
            lines.append('  exact ' + ('z1' if nb == 1 else '⟨' + ', '.join(f'h{j+1}' if T[j] else f'z{j+1}' for j in range(nb)) + '⟩'))
            out.append('\n'.join(lines) + '\n')
    # main
    vars_ = ' '.join(map(str, b + xs))
    hyps = []
    for i in range(1, nb+1):
        hyps.append(f'(hQ{i} : {hypQ[i-1]} = 0)'); hyps.append(f'(hH{i} : {hypH[i-1]} = 0)')
    main = [f'theorem core{d} {{K : Type*}} [Field K] [CharZero K] ({vars_} : K)\n    ' + '\n    '.join(hyps) +
            ' :\n    ' + ' ∧ '.join(f'{v} = 0' for v in b) + ' := by']
    for i in range(1, nb+1):
        main.append(f'  have g{i} := (mul_eq_zero.mp (core{d}_r{i} {bs} x{i} hQ{i} hH{i})).resolve_left (by norm_num)')
        if split:
            main.append(f'  have c{i} : {b[i-1]} = 0 ∨ RPI.Poly.eval {bl} S{d}_{i} = 0 := by\n'
                        f'    rcases mul_eq_zero.mp g{i} with h | h\n'
                        f'    · exact Or.inl (pow_eq_zero_iff (n := {M[i-1]}) (by norm_num) |>.mp h)\n'
                        f'    · exact Or.inr h')
        else:
            main.append(f'  rw [pow_zero, one_mul] at g{i}')
    hs = ' '.join(f'{"h" if split else "g"}{i}' for i in range(1, nb+1))
    if split:
        rc = ' <;> '.join(f'rcases c{i} with h{i} | h{i}' for i in range(1, nb+1))
        main.append(f'  {rc}')
        for T in itertools.product([1, 0], repeat=nb):
            tag = ''.join(map(str, T))
            if all(T):
                main.append('  · exact ' + ('h1' if nb == 1 else '⟨' + ', '.join(f'h{i}' for i in range(1, nb+1)) + '⟩'))
            else:
                main.append(f'  · exact core{d}_case{tag} {bs} {hs}')
    else:
        tag = '0' * nb
        for j, e in zl:
            main.append(f'  have z{j+1} : {b[j]} = 0 := pow_eq_zero_iff (n := {e}) (by norm_num) |>.mp\n'
                        f'    ((mul_eq_zero.mp (core{d}_c{tag}_{j+1} {bs} {hs})).resolve_left (by norm_num))')
        main.append('  exact ' + ('z1' if nb == 1 else '⟨' + ', '.join(f'z{j+1}' for j in range(nb)) + '⟩'))
    out.append('\n'.join(main))
    print(f'-- d={d} split={split} stats {stats}', file=log)
    return '\n'.join(out), stats
