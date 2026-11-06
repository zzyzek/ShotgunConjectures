# OEIS A141459, A211163: denominators of ∫_0^1 log(1 - 1/x)^n dx

**Source.** [A141459](https://oeis.org/A141459): a(n) = Π_{p odd prime, p-1 | n} p (a(0) = 1). Comment:
"Conjecture: a(n) = denominator of integral_{0..1}(log(1-1/x)^n) dx" (J.-F. Alcover, Feb 01 2013).
[A211163](https://oeis.org/A211163) (J.-F. Alcover, Jan 30 2013): numerator of
(-1/Pi^n) * integral_{0..1} (log(1-1/x)^n) dx, n ≥ 2; "Conjecture: sequence of denominators is A141459."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** On (0,1), 1 - 1/x < 0, so log is the principal complex logarithm (the reading behind the
entries' data: for n = 2 the integral is -2π²/3). The integral is a rational multiple of (πi)^n, and
"denominator" is the denominator of that rational; for A211163 it is the denominator of the rational
number (-1/π^n)·∫ (which is 0 for odd n ≥ 3).

**Result.** True: ∫_0^1 log(1 - 1/x)^n dx = 2^n B'_n (πi)^n for all n ≥ 0 (B'_n the Bernoulli numbers
with B'_1 = +1/2), and den(2^n B'_n) = A141459(n). Hence both conjectures hold (A211163 for n ≥ 2, where
(-1/π^n)·∫ = -2^n B'_n i^n is rational).

**Argument.**
1. With x = 1/(1+e^t), 1 - 1/x = -e^t and log(-e^t) = t + πi, so the integral is
   ∫_ℝ ρ(t)(t + πi)^n dt with ρ(t) = e^t/(1+e^t)^2 (logistic density).
2. Moments μ_j = ∫ ρ t^j: μ_0 = 1, μ_odd = 0 (ρ is even), and for j = 2k ≥ 2,
   μ_2k = 2∫_0^∞ ρ(s) s^2k ds = 2 Σ_m (-1)^(m+1) m ∫_0^∞ s^2k e^(-ms) ds = 2 (2k)! η(2k)
   = (-1)^(k+1)(2^2k - 2) π^2k B_2k (η(2k) = (1 - 2^(1-2k)) ζ(2k)). In one formula,
   μ_j = -(2^j - 2) B'_j (πi)^j.
3. Binomial expansion: ∫ = (πi)^n Σ_j C(n,j)(2 - 2^j) B'_j, and Σ_j C(n,j)(2 - 2^j) B'_j = 2^n B'_n
   (exponential generating functions: e^x(2B'(x) - B'(2x)) = B'(2x) with B'(x) = x e^x/(e^x - 1)).
4. von Staudt–Clausen: for k ≥ 1 the denominator of B_2k is Π_{p-1 | 2k} p, each prime once; the
   factor 2^2k removes p = 2 and leaves the odd primes. For odd n ≥ 3, B'_n = 0 (denominator 1, and no
   odd p has p - 1 | n); n = 0, 1 give 1.

**Evidence.**
- Lean (Mathlib): [`A141459_mathlib.lean`](A141459_mathlib.lean). Main theorems `integral_formula`,
  `A141459_eq_den`, `A141459_conjecture` (∫ = q (πi)^n ⇒ q.den = A141459 n) and `A211163_conjecture`
  (n ≥ 2, (-1/π^n)∫ = r ⇒ r.den = A141459 n), with the integral written as
  `∫ x in (0:ℝ)..1, (Complex.log (1 - 1/(x:ℂ)))^n`. Uses Mathlib's `Bernoulli.vonStaudt_clausen`,
  `padicValRat_bernoulli`, `hasSum_zeta_nat`, the Gamma integral and the one-dimensional change of
  variables. Axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: den(2^n B'_n) against the b-file (n ≤ 300), the A211163 data terms, and the
  integral numerically (mpmath, n ≤ 8).
- Outside Lean: only the reading (principal complex logarithm; "denominator" of the rational factor).

**Review level.** lean-proof.

**Prior art.** Checked 2026-11-06. The entries still state the conjectures. Luschny's formula in A141459,
a(n) = denominator(0^n + Σ ζ(1-j)(2^j-2) j C(n,j)), is the rational 1 - Σ C(n,j)(2^j - 2)B_j of step 3,
but the entries do not connect it to the integral. The ingredients (logistic moments via η(2k),
von Staudt–Clausen) are classical; no statement of this integral's value or of the conjecture's proof
was found. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
