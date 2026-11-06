# OEIS A212425, A212392: ((b−1)(n−1)+1) divides the coefficients of A(x) = (x + A(A(x)))^b

**Source.** OEIS [A212425](https://oeis.org/A212425) (b = 3, A(x) = sum a(n) x^(8n−5)), "Conjecture: (2*n-1)
divides a(n)", and OEIS [A212392](https://oeis.org/A212392) (b = 2, A(x) = sum a(n) x^(3n−1)), "Conjecture: n
divides a(n)" (P. D. Hanna, May 2012). Both entries add the general form: if A(x) = (x + A(A(x)))^b with
A(x) = sum a(n) x^((b^2−1)(n−1)+b), then ((b−1)(n−1)+1) divides a(n). (OEIS text, CC BY-SA 4.0, revisions
#20 and #19 of Oct 30 2026; still conjectures on 2026-11-06.) A212426 and A212391 list the quotients.

**Result.** True for every b ≥ 2 (so both conjectures and the general form).

**Argument.** Let F = A, u = x + F(F(x)), so F = u^b, and let J be the formal antiderivative of (b+1)F (rational
coefficients, J(0) = 0).
1. *Identity.* J(x) − J(F(x)) = u^(b+1) − (b+1) F(x) F(F(x)). Both sides vanish at 0. Derivatives (chain rule):
   left (b+1)F − (b+1)F(F)·F'; right (b+1)u^b u' − (b+1)[F'·F(F) + F·F'(F)·F'] with u^b = F and
   u' = 1 + F'(F)·F', which is the same.
2. *Integrality.* The right side has integer coefficients. F = u^b with u(0) = 0, so x^b, hence x^2, divides F.
   The coefficient of x^n in J(F(x)) = sum_d j_d F^d only involves j_d with 2d ≤ n, i.e. d < n. By induction on
   n every coefficient j_n of J is an integer.
3. *Reading off.* j_(k+1) = (b+1) [x^k]F/(k+1). At k = (b^2−1)(n−1)+b, k+1 = (b+1)((b−1)(n−1)+1), so
   ((b−1)(n−1)+1) divides a(n).

**Evidence.**
- Lean (Mathlib): [`A212425_mathlib.lean`](A212425_mathlib.lean). For any b ≥ 2 and any F ∈ ℤ⟦X⟧ with
  constant coefficient 0 and `F = (X + F.subst F)^b`: `A212425_dvd_all` ((k+1) ∣ (b+1)[x^k]F for all k),
  `A212425_main` (the general conjecture), `A212425_b3` ((2n−1) ∣ [x^(8n−5)]F, A212425), `A212392_b2`
  (n ∣ [x^(3n−1)]F, A212392). Lemmas `A212425_identity` (step 1, via Mathlib's `derivative_subst`),
  `A212425_integral` (step 2). Axioms: propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): computes the solution for b = 2..6 to degree 120–150, checks the
  OEIS data (b = 2, 3), the identity of step 1 and the divisibility for every computed coefficient.
- Outside Lean: existence of the solution F (the theorems hold for every solution). Existence and uniqueness
  with integer coefficients are Lemma 7.1 of Abbondandolo and Majer (arXiv:2610.33287), and also follow from the
  recursion: the coefficient of x^j on the right depends only on coefficients of F of degree < j.

**Review level.** `lean-proof` (modulo existence of the g.f., stated above).

**Prior art.** Checked 2026-11-06: OEIS A212425, A212392, A212426, A212391 entries; A. Abbondandolo and
P. Majer, "Gibbs measures on Cayley trees and homoclinic orbits", arXiv:2610.33287 (2026), Remark 7.2 (linked
from both entries) meets these series as invariant graphs of an area-preserving map but does not discuss
divisibility; web search found no proof. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
