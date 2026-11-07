# OEIS A183161: the self-convolution square root of A183160 has no term ≡ 3 (mod 4)

**Source.** [A183161](https://oeis.org/A183161) (Hanna, 2010): a(0) = 1 and
sum_{k=0..n} a(k) a(n-k) = A183160(n) = sum_{k=0..n} C(n+k, n-k) C(2n-k, k); a = 1, 1, 5, 26, 145, 841, ...
Comment: "Conjecture: a(n) is never congruent to 3 modulo 4; see A218622." (Hanna, Nov 03 2012;
OEIS text checked 2026-11-07 from the cached entry.) The same claim is A218622 and, for the shifted family, A219197.

**Result.** True. a(n) mod 4 is computed by a six-state automaton reading the binary digits of n from the
least significant end: states 0..5, start 0, transitions on digit 0: (0, 0, 3, 4, 4, 5), on digit 1: (1, 2, 2, 5, 3, 5),
outputs (1, 1, 2, 2, 2, 0). No output is 3. In particular a(n) is odd iff n AND 2n = 0, and then a(n) ≡ 1 (mod 4).

**Argument.** Put J = 1/(1-t), x = t(1-t)^2, and write ψ for the substitution x ↦ t(1-t)^2.
1. *Lagrange inversion.* For every F ∈ ℤ[[x]], [x^n] F = [t^n] ψ(F) (1-3t) J^(2n+1). Both sides are linear in F and see
   only F_0..F_n; for F = x^m, m ≤ n, the right side is [t^(n-m)] (1-3t) J^(2(n-m)+1) = [n = m], because
   C(3d, d) = 3 C(3d-1, d-1) for d ≥ 1.
2. *A183160.* (1+t) sum_k C(N-k, k) t^k (1-t)^(N-2k) = 1 - (-t)^(N+1) (both sides satisfy f(N+2) = (1-t) f(N+1) + t f(N)
   by Pascal's rule). With C(n+k, n-k) = [t^n] t^k J^(2k+1) this gives A183160(n) = [t^n] J^(2n+1)/(1+t).
3. *The square root.* Let A = sum a(n) x^n. By 1 and 2, [t^n] (ψ(A)^2 (1-3t) - 1/(1+t)) J^(2n+1) = 0 for all n, and
   H ↦ ([t^n] H J^(2n+1))_n is injective (triangular), so S = ψ(A)(1-3t) satisfies S(0) = 1, S^2 (1+t) = 1-3t, and
   a(n) = [t^n] S J^(2n+1) = sum_j s_j C(3n-j, n-j).
4. *S mod 4.* S ≡ 1 (mod 2); writing S = 1 + 2E gives (E + E^2)(1+t) = -t exactly. W = sum_{m ≥ 1, v_2(m) even} t^m
   satisfies (1-t)(W + W(t^2)) = t and W^2 ≡ W(t^2) (mod 2), so (E - W)(1 + E + W) ≡ 0 (mod 2), E ≡ W (mod 2) and
   S ≡ 1 + 2W (mod 4).
5. *Automaton.* a(n) ≡ [x^n t^n] F (mod 4) with F = (1+2W)(1-t)/((1-t)^2 - x) = (N0 + N1 W)/Q^2, Q = (1-t)((1-t)^2 - x),
   N0 = (1-t)^2 Q, N1 = 2 N0. Over ℤ/4, Q^4 = Q(x^2, t^2)^2 and Q^2 W = t(1-t)((1-t)^2-x)^2 - Q^2 W(t^2), so the Cartier
   operators Λ_r (coefficient (i, j) ↦ (2i+r, 2j+r)) satisfy Λ_r((N0 + N1 W)/Q^2) = (N0' + N1' W)/Q^2 with
   N0' = Λ_r(N0 Q^2 + N1 t(1-t)B^2), N1' = Λ_r(-N1 Q^2) (Rowland-Yassawi). Starting from (N0, N1), these maps close
   on six numerator pairs; the diagonal's value at 0 is N0(0, 0) ∈ {1, 1, 2, 2, 2, 0}.

**Evidence.**
- Lean: [`A183161_mathlib.lean`](A183161_mathlib.lean), theorem `A183161_mod4` (from the definition: any integer
  sequence with a(0) = 1 and self-convolution A183160) and `A183161_gf_mod4` (from Hanna's g.f.). The proof is in the
  library: `OpenProblemsLib.HannaMod4` (steps 1-5; `lagrange`, `fibT_closed`, `A183160_eq`, `kernel_inj`, `S_mod4`,
  `step_ok` by `decide`) on top of `OpenProblemsLib.AutomaticMod` (Cartier operators, `ry_step`,
  `automaton_induction`, guide [lib/docs/automatic-mod.md](../../lib/docs/automatic-mod.md)). Axioms: propext,
  Classical.choice, Quot.sound.
- [`certificate/gf_check.py`](certificate/gf_check.py): Hanna's g.f. formula, the square roots, "never 3" and the
  automaton against the definition for n ≤ 300. [`certificate/ry_automaton.py`](certificate/ry_automaton.py): the
  script that found the six states (prints the Lean literals).
- Outside Lean: the existence of the integer sequence (the OEIS terms); the Lean theorems hold for every integer
  sequence with the defining property.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: the entry still lists the conjecture; google-deepmind/formal-conjectures (clone of
2026-11-06) and otoi-lab/oeis-lean-proofs have no A183161/A218622/A219197 file; web search (2026-11-06, r15) found
no proof. The automaton method is Rowland-Yassawi, J. Théor. Nombres Bordeaux 27 (2015).
