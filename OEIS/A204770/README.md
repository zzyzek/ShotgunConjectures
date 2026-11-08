# OEIS A204770: the zero terms have density 1 (follows from standard theory)

**Source.** OEIS [A204770](https://oeis.org/A204770) (expansion of psi(x^3) f(−x), Ramanujan
theta functions; g.f. Π_{k>0} (1 − x^k)(1 − x^{6k})/(1 − x^{6k−3})), comment by Michael Somos:
"Conjecture: density of zero terms slowly approaches 1." (OEIS text, CC BY-SA 4.0.)

**Result.** True: #{n < N : a(n) ≠ 0} = O(N/√(log N)).

**Argument.** Euler's pentagonal theorem f(−x) = Σ_{k∈ℤ} (−1)^k x^{k(3k−1)/2} and Gauss's
psi(x) = Σ_{j≥0} x^{j(j+1)/2} give

  a(n) = Σ (−1)^k over k ∈ ℤ, j ≥ 0 with k(3k−1)/2 + 3j(j+1)/2 = n.

Multiplying by 24 and adding 10: (6k − 1)² + 9(2j + 1)² = 24n + 10. So a(n) ≠ 0 forces
24n + 10 = u² + (3v)² to be a sum of two squares. By Landau's theorem the number of integers
m ≤ x that are sums of two squares is ~ C x/√(log x), so at most O(N/√(log N)) of the n < N
have a(n) ≠ 0. (Without Landau: for each prime q ≡ 3 (mod 4), q ≠ 3, the n with q exactly
dividing 24n + 10 have density (q − 1)/q², these events are independent by the Chinese
remainder theorem, and Σ 1/q over such q diverges by Dirichlet's theorem, so the density of
the n avoiding all of them is 0.) The rate 1/√(log N) matches "slowly": the fraction of
nonzero terms is 0.65, 0.52, 0.47, 0.43 for N = 10², 10³, 5·10³, 2·10⁴.

More generally, the g.f. is q^{−5/12} η(q)η(q⁶)²/η(q³), a holomorphic modular form of weight 1,
and Serre (1976) showed that the coefficients of every weight-1 form vanish on a set of
density 1; the computation above is the explicit form of that fact for this entry.

**Evidence.**
- Lean (Mathlib + `OpenProblemsLib.PNTApps`): [`A204770_mathlib.lean`](A204770_mathlib.lean), the conjecture via
  the parenthetical "without Landau" route above. a(n) is defined as the coefficient of x^n in
  psi(x^3) f(-x) with the theta series psi(q) = sum_{j>=0} q^(j(j+1)/2), f(-q) = sum_{k in Z} (-1)^k q^(k(3k-1)/2)
  (the entry's name; the product form is not used). `A204770_sq_add_sq`: a(n) ≠ 0 implies 24n + 10 is a sum
  of two squares; `not_sq_add_sq_of_exact` (from Mathlib `Nat.eq_sq_add_sq_iff`); `count_G` (q - 1 residues
  n mod q^2 with q exactly dividing 24n + 10); `A204770_nonzero_density_zero` (library
  `density_zero_of_sieve` with Dirichlet's divergence for q ≡ 3 mod 4) and `A204770_zero_density_one`:
  #{n < N : a(n) = 0}/N → 1. Checked 2026-11-08 with `tools/leancheck-mathlib.sh`: OK, axioms propext,
  Classical.choice, Quot.sound.
- `certificate/check.py`: the product and the theta-sum agree for n ≤ 20 000 and match the data; every
  n ≤ 20 000 with a(n) ≠ 0 has 24n + 10 a sum of two squares; fractions above.
- Outside Lean: none for the density-one statement (the rate O(N/sqrt(log N)), which uses Landau's theorem,
  and the equality with the product form of the g.f. are not formalised).

**Review level.** `lean-proof` (density 1 of the zero terms proved in Lean; the O(N/sqrt(log N)) rate is a paper argument).

**Prior art.** The conjecture is a direct instance of Serre's lacunarity theorem for weight-1
forms (J.-P. Serre, "Divisibilité de certaines fonctions arithmétiques", Enseignement Math.
22 (1976)); the entry does not mention it (cached entry, checked 2026-11-07).
google-deepmind/formal-conjectures (clone of 2026-11-06) and otoi-lab/oeis-lean-proofs have no
file for A204770. A natural sharper question, an asymptotic C·N/√(log N) for the number of
nonzero terms (cancellation among representations can create extra zeros), is not addressed.
