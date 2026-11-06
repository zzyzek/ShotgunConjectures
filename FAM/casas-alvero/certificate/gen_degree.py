"""Emit the Lean section for one degree d: core<d> (from gen_lean.core) plus
casas_alvero_root_deg_<d> and casas_alvero_deg_<d>. All linear_combination identities are
checked with sympy here first."""
import sys
from sympy import symbols, binomial, expand, diff, factorial, Integer
import gen_lean

# Optional hook d -> (core text, stats); None uses the linear_combination cores.
CORE = None

def L(e): return gen_lean.lean(expand(e))

def section(d):
    out = []
    c = symbols(' '.join(f'c{j}' for j in range(d)), seq=True)
    X = symbols(' '.join(f'x{i}' for i in range(1, d)), seq=True)
    a = X[d-2]
    t = symbols('t')
    P = t**d + sum(c[j]*t**j for j in range(d))
    def H(i, x): return expand((diff(P, t, i)/factorial(i)).subs(t, x))
    # b_j = Taylor coefficients at a
    cc = list(c) + [Integer(1)]
    B = [expand(sum(binomial(n, j)*cc[n]*a**(n-j) for n in range(j, d+1))) for j in range(d+1)]
    assert expand(B[0] - P.subs(t, a)) == 0 and expand(B[d-1] - H(d-1, a)) == 0
    pA = P.subs(t, a); qA = H(d-1, a)
    stats = None
    if d >= 3:
        import os
        cache = f'core{d}.lean.in'
        if CORE is not None:
            # reflective certificates (gen_reflect_degree.py sets this hook)
            core_txt, stats = CORE(d)
            out.append(core_txt + '\n')
        elif d >= 6:
            import gen_cases
            core_txt, stats = gen_cases.core_cases(d)
            out.append(core_txt + '\n')
        elif os.path.exists(cache):
            core_txt, stats = open(cache).read().rstrip('\n'), 'cached'
        else:
            core_txt, stats = gen_lean.core(d)
        if d < 6 and CORE is None:
            import split_core
            out.append(split_core.split_core(core_txt, d) + '\n')
    # root version
    out.append(f'theorem casas_alvero_root_deg_{d} [CharZero K] (P : K[X]) (hP : P.Monic)\n'
               f'    (hd : P.natDegree = {d}) (h : HasCasasAlveroPropR P) : ∃ a, P = (X - C a) ^ {d} := by')
    out.append(f'  have hh : ∀ i < {d}, ∃ α, P.eval α = 0 ∧ (P.hasseDeriv i).eval α = 0 := fun i hi => by\n'
               f'    obtain ⟨α, h1, h2⟩ := h i (by simp [hd, hi])\n'
               f'    exact ⟨α, h1, h2⟩')
    out.append(f'  have cd : P.coeff {d} = 1 := by rw [← hd]; exact hP.coeff_natDegree')
    ps = ' '.join(f'p{i}' for i in range(1, d)); qs = ' '.join(f'q{i}' for i in range(1, d))
    for i in range(1, d):
        out.append(f'  obtain ⟨x{i}, p{i}, q{i}⟩ := hh {i} (by norm_num)')
    out.append(f'  rw [eval_eq_sum_range\' (n := {d+1}) (by omega)] at {ps}')
    out.append(f'  rw [eval_hasseDeriv_sum P hd] at {qs}')
    out.append(f'  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at {ps} {qs}')
    out.append(f'  norm_num [Nat.choose, cd] at {ps} {qs}')
    for j in range(d):
        out.append(f'  set c{j} := P.coeff {j} with hc{j}')
    pa, qa = f'p{d-1}', f'q{d-1}'
    if d >= 3:
        args = ' '.join(f'({L(B[j])})' for j in range(1, d-1)) + ' ' + \
               ' '.join(f'(x{i} - {a})' for i in range(1, d-1))
        b = symbols(' '.join(f'b{j}' for j in range(1, d-1)), seq=True)
        Qt = t**d + sum(b[j-1]*t**j for j in range(1, d-1))
        sub = {b[j-1]: B[j] for j in range(1, d-1)}
        hyps = []
        for i in range(1, d-1):
            x = X[i-1]
            # hQ_i
            goal = expand(Qt.subs(t, x - a).subs(sub))
            comb = P.subs(t, x) - pA - (x - a)**(d-1)*qA
            assert expand(goal - comb) == 0
            hyps.append(f'(by linear_combination p{i} - {pa} - (x{i} - {a})^{d-1} * {qa})')
            goal = expand((diff(Qt, t, i)/factorial(i)).subs(t, x - a).subs(sub))
            k = binomial(d-1, i)
            comb = H(i, x) - k*(x - a)**(d-1-i)*qA
            assert expand(goal - comb) == 0
            hyps.append(f'(by linear_combination q{i} - {k} * (x{i} - {a})^{d-1-i} * {qa})')
        zs = ', '.join(f'z{j}' for j in range(1, d-1))
        out.append(f'  obtain {zs if d == 3 else "⟨" + zs + "⟩"} := core{d} {args}\n    ' + '\n    '.join(hyps))
    out.append(f'  refine ⟨{a}, eq_X_sub_C_pow P hP hd {a} ?_⟩')
    out.append('  intro j hj')
    out.append('  interval_cases j')
    hname = {0: pa, d-1: qa}
    for j in range(1, d-1): hname[j] = f'z{j}'
    for j in range(d):
        terms = []
        comb = 0
        for n in range(j, d):
            co = binomial(n, j)*(-a)**(n-j)
            Bn = B[n]
            comb += co*Bn
            terms.append(f'({L(co)}) * {hname[n]}')
        goal = c[j] - binomial(d, j)*(-a)**(d-j)
        assert expand(goal - comb) == 0, j
        out.append(f'  · norm_num [Nat.choose]\n    linear_combination ' + ' + '.join(terms))
    out.append('')
    out.append(f'/-- Casas-Alvero in degree {d}, in the formal-conjectures statement shape. -/')
    out.append(f'theorem casas_alvero_deg_{d} [CharZero K] (P : K[X]) (hP : P.Monic) (hd : P.natDegree = {d})\n'
               f'    (hca : HasCasasAlveroProp P) : ∃ α : K, P = (X - C α) ^ P.natDegree :=\n'
               f'  of_algClosure P hP hd hca fun Q hQ hQd hQr => casas_alvero_root_deg_{d} Q hQ hQd hQr\n')
    return '\n'.join(out), stats

if __name__ == '__main__':
    parts = [open('header.lean').read()]
    for d in map(int, sys.argv[1:]):
        txt, st = section(d)
        print(f'-- d={d} stats {st}', file=sys.stderr)
        parts.append(txt)
    
    print('\n'.join(parts))
