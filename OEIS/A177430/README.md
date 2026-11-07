# OEIS A177430 / A177431: exp(sum b(n)^m x^n/n) is integral exactly for even m >= 0

**Source.** [A177431](https://oeis.org/A177431) b = 1, 3, 4, 5, 6, 12, ... and [A177430](https://oeis.org/A177430)
= b^2 (Hanna, 2010): the least increasing sequence of squares that is the logarithmic derivative of an integer
series, i.e. exp(sum b(n)^2 x^n/n) is in Z[[x]]. Conjectures: A177431, "exp(Sum a(n)^m x^n/n) consists entirely of
integer coefficients only when m is a nonnegative even integer"; A177430, "{a(n)^(m/2)} forms a logarithmic
derivative of an integer sequence only when m is a nonnegative even integer" (same statement, since
A177430(n)^(m/2) = b(n)^m). (OEIS text checked 2026-11-06.)

**Reading.** m ranges over the integers.

**Result.** True, in both directions: exp(sum b(n)^m x^n/n) is integral iff m >= 0 and m is even.

**Argument.** Integrality of exp(sum c(n) x^n/n) for integer c is equivalent to the Gauss congruences
p^a | c(m p^a) - c(m p^(a-1)) (Dwork). 
- m even >= 0: b^2 satisfies them (definition of b), and they are closed under products, so b^m = (b^2)^(m/2) does.
- m odd >= 1: at p = 2, a = 2, m' = 1 the congruence needs 4 | b(4)^m - b(2)^m = 5^m - 3^m, but 5^m - 3^m = 2
  (mod 4) for odd m. (The x^4 coefficient is not integral.)
- m < 0: the x^2 coefficient is (b(1)^2m + b(2)^m)/2 = (1 + 3^m)/2 with 0 < 3^m < 1, not an integer.

**Evidence.**
- Lean (Mathlib): [`A177430_mathlib.lean`](A177430_mathlib.lean), using `OpenProblemsLib.Dwork`
  (`gauss_of_expCoeff_int`, `LGp_pow`, `expCoeff_int_of_gauss`) and `OpenProblemsLib.DworkLocal` (`expQ`,
  `expQ_cast`). Main theorem `A177431_iff`: for b : ℕ → ℕ with b 1 = 1, b 2 = 3, b 4 = 5 and
  exp(sum b(n)^2 x^n/n) integral, for all m : ℤ, (∀ n, expQ (b^m) n ∈ ℤ) ↔ (0 ≤ m ∧ Even m). Check
  `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/greedy.py`](certificate/greedy.py): recomputes the greedy sequence (24 terms, equal to the
  data) and the first non-integral coefficient for m = -2..8 (index 2 for m < 0, 4 for odd m, none for even m).
- Outside Lean: that the greedy definition gives b(1), b(2), b(4) = 1, 3, 5 (greedy.py; the entry's data).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entries (both still "Conjecture"); not in google-deepmind/formal-conjectures
or otoi-lab/oeis-lean-proofs. Gauss congruences and their closure under products are classical (Dwork; e.g.
Zarelua, Minton); the application to this sequence is immediate.
