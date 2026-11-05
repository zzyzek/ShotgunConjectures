"""Core lemma for degree d by case split (used for d >= 6).

Stage 1 (per i): N_i * b_i^m_i * S_i(b) = U Q(x_i) + V H_i(x_i), where Res_x(Q, H_i) = c b_i^m_i S_i.
So b_i = 0 or S_i = 0. Stage 2 (per case T = set of i with b_i = 0, and per j not in T):
N b_j^e = sum_{i in T} g_i b_i + sum_{i not in T} g_i S_i. One Lean declaration per identity.
"""
import itertools
from sympy import symbols, Poly, diff, factorial, expand, resultant, factor_list, QQ
import gen_lean
from gen_lean import lean, solve_member

def big(comb):
    return 'set_option maxHeartbeats 0 in\n' if len(comb) > 20000 else ''

def core_cases(d, maxe=80):
    t = symbols('t')
    b = list(symbols(' '.join(f'b{j}' for j in range(1, d-1)), seq=True))
    xs = list(symbols(' '.join(f'x{i}' for i in range(1, d-1)), seq=True))
    nb = d - 2
    W = [d - j for j in range(1, d-1)]
    Qt = t**d + sum(b[j-1]*t**j for j in range(1, d-1))
    Ht = [expand(diff(Qt, t, i)/factorial(i)) for i in range(1, d-1)]
    bs = ' '.join(map(str, b))
    out, S, M, SW = [], [], [], []
    hypQ, hypH = [], []
    for i in range(1, nb+1):
        x = xs[i-1]
        R = resultant(Qt, Ht[i-1], t)
        fl = factor_list(R)[1]
        m = [mm for f, mm in fl if f == b[i-1]][0]
        Sf = [f for f, mm in fl if f != b[i-1]]
        assert len(Sf) == 1
        Si = Poly(Sf[0], *b, domain=QQ)
        S.append(Si); M.append(m)
        SW.append(sum(e*w for e, w in zip(Si.monoms()[0], W)))
        V1 = b + [x]; W1 = W + [1]
        Qx = Poly(Qt.subs(t, x), *V1, domain=QQ); Hx = Poly(Ht[i-1].subs(t, x), *V1, domain=QQ)
        tgt = Poly(b[i-1]**m * Si.as_expr(), *V1, domain=QQ)
        den, (U, Vv) = solve_member([Qx, Hx], [d, d-i], V1, W1, tgt, d*(d-i))
        hq = lean(expand(Qt.subs(t, x))); hh = lean(expand(Ht[i-1].subs(t, x)))
        hypQ.append(hq); hypH.append(hh)
        comb = f'linear_combination ({lean(U)}) * hQ{i} + ({lean(Vv)}) * hH{i}'
        out.append(f'{big(comb)}theorem core{d}_r{i} {{K : Type*}} [Field K] ({bs} {x} : K)\n'
                   f'    (hQ{i} : {hq} = 0) (hH{i} : {hh} = 0) :\n'
                   f'    ({den}:K) * ({b[i-1]}^{m} * ({lean(Si)})) = 0 := by\n  {comb}\n')
    stats = []
    masks = list(itertools.product([0, 1], repeat=nb))
    for T in masks:
        if all(T): continue
        tag = ''.join(map(str, T))
        gens = [Poly(b[i], *b, domain=QQ) if T[i] else S[i] for i in range(nb)]
        gw = [W[i] if T[i] else SW[i] for i in range(nb)]
        hyps = ' '.join(f'(h{i+1} : {b[i]} = 0)' if T[i] else f'(h{i+1} : ({lean(S[i])}) = 0)' for i in range(nb))
        zl = []
        for j in range(nb):
            if T[j]: continue
            for e in range(1, maxe+1):
                r = solve_member(gens, gw, b, W, Poly(b[j]**e, *b, domain=QQ), e*W[j])
                if r: break
            assert r, (T, j)
            den, cof = r
            stats.append((tag, j+1, e, len(str(den))))
            comb = 'linear_combination ' + ' + '.join(f'({lean(c)}) * h{k+1}' for k, c in enumerate(cof) if not c.is_zero)
            out.append(f'{big(comb)}theorem core{d}_c{tag}_{j+1} {{K : Type*}} [Field K] ({bs} : K)\n'
                       f'    {hyps} :\n    ({den}:K) * {b[j]}^{e} = 0 := by\n  {comb}\n')
            zl.append((j, e))
        # case lemma: all b = 0
        lines = [f'theorem core{d}_case{tag} {{K : Type*}} [Field K] [CharZero K] ({bs} : K)\n'
                 f'    {hyps} :\n    ' + ' ∧ '.join(f'{v} = 0' for v in b) + ' := by']
        hs = ' '.join(f'h{i+1}' for i in range(nb))
        for j, e in zl:
            lines.append(f'  have z{j+1} : {b[j]} = 0 := pow_eq_zero_iff (n := {e}) (by norm_num) |>.mp\n'
                         f'    ((mul_eq_zero.mp (core{d}_c{tag}_{j+1} {bs} {hs})).resolve_left (by norm_num))')
        lines.append('  exact ⟨' + ', '.join(f'h{j+1}' if T[j] else f'z{j+1}' for j in range(nb)) + '⟩')
        out.append('\n'.join(lines) + '\n')
    # main
    vars_ = ' '.join(map(str, b + xs))
    hyps = []
    for i in range(1, nb+1):
        hyps.append(f'(hQ{i} : {hypQ[i-1]} = 0)'); hyps.append(f'(hH{i} : {hypH[i-1]} = 0)')
    main = [f'theorem core{d} {{K : Type*}} [Field K] [CharZero K] ({vars_} : K)\n    ' + '\n    '.join(hyps) +
            ' :\n    ' + ' ∧ '.join(f'{v} = 0' for v in b) + ' := by']
    for i in range(1, nb+1):
        main.append(f'  have g{i} := (mul_eq_zero.mp (core{d}_r{i} {bs} x{i} hQ{i} hH{i})).resolve_left (by norm_num)\n'
                    f'  have c{i} : {b[i-1]} = 0 ∨ ({lean(S[i-1])}) = 0 := by\n'
                    f'    rcases mul_eq_zero.mp g{i} with h | h\n'
                    f'    · exact Or.inl (pow_eq_zero_iff (n := {M[i-1]}) (by norm_num) |>.mp h)\n'
                    f'    · exact Or.inr h')
    rc = ' <;> '.join(f'rcases c{i} with h{i} | h{i}' for i in range(1, nb+1))
    main.append(f'  {rc}')
    hs = ' '.join(f'h{i}' for i in range(1, nb+1))
    # rcases order: Or.inl (b_i = 0) first -> T bit 1 first
    for T in itertools.product([1, 0], repeat=nb):
        tag = ''.join(map(str, T))
        if all(T):
            main.append('  · exact ⟨' + ', '.join(f'h{i}' for i in range(1, nb+1)) + '⟩')
        else:
            main.append(f'  · exact core{d}_case{tag} {bs} {hs}')
    out.append('\n'.join(main))
    return '\n'.join(out), stats
