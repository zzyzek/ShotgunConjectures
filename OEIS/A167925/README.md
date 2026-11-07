# OEIS A167925: Daddi's coefficient conjecture is now the definition, and the two closed forms agree

**Source.** OEIS [A167925](https://oeis.org/A167925) (Bagula 2009; keyword obsc until 2023). Comment
(Daddi 2011): "Conjecture: a(6),…,a(9) = coefficient of x^2 in the Maclaurin expansion of
1/(n*x^2+n*x+1) for n=1,2,3,4; a(10..14) = −coefficient of x^3 … Etc." On 2023-09-11 G. C. Greubel
removed Bagula's program ("did not produce the data") and turned the conjecture into the formula
T(n, k) = (−1)^(n+1) [x^(n−1)] 1/(1 + (k+1)x + (k+1)x^2); the name is now
T(n, k) = sqrt(k+1)^(n−1) ChebyshevU(n−1, sqrt(k+1)/2).

**Reading.** The original generator is lost (its program did not reproduce the data), so the claim
can only be read against the data and the current name.

**Result.** The conjecture holds for all 55 data terms and agrees with the current name for all
n ≥ 1, k ≥ 0.

**Argument.** With a = k + 1, both s^m U_m(s/2) (s² = a) and (−1)^m [x^m] 1/(1 + ax + ax²) satisfy
V_{m+2} = aV_{m+1} − aV_m, V_0 = 1, V_1 = a.

**Evidence.** Lean (Mathlib): [`A167925_mathlib.lean`](A167925_mathlib.lean), `A167925_main`
(Chebyshev form = (−1)^(n+1)·coefficient, n ≥ 1), `A167925_cheb`, `A167925_series`
((1 + aX + aX²)·Σ(−1)^m V_m X^m = 1), `A167925_data` (rows 0..9 = the data). Axioms propext,
Classical.choice, Quot.sound. Outside Lean: none for the stated identities; the original 2009
definition cannot be checked.

**Review level.** `lean-proof`.

**Prior art.** Greubel's 2023 edit (formula given without proof). Not in formal-conjectures or
oeis-lean-proofs (2026-11-07).
