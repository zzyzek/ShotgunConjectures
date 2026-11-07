# OEIS A219543 and A218755: Bernoulli denominators ≡ 3 or 6 (mod 9) differ by multiples of 36

**Source.** OEIS [A219543](https://oeis.org/A219543) (denominators of Bernoulli numbers ≡ 3 mod 9) and
[A218755](https://oeis.org/A218755) (≡ 6 mod 9), both subsets of A090801 (distinct Bernoulli denominators).
Each entry: "Conjecture: all the first differences ... of the sequence are multiples of 36." (OEIS text,
CC BY-SA 4.0.)

**Result.** True, and answered in both entries: Charles R. Greathouse IV (Nov 22 2012), "The conjecture is
true, since elements of A090801 are 2 mod 4."

**Argument.** The denominators of B₀, B₁ and of B_j for odd j ≥ 3 are 1, 2, 1, which are not ≡ 3 or 6 (mod 9).
For k ≥ 1, von Staudt–Clausen gives that 2 divides the denominator of B_{2k} and 4 does not, so it is
≡ 2 (mod 4). With ≡ 3 (mod 9) this gives ≡ 30 (mod 36) (A219543); with ≡ 6 (mod 9) it gives ≡ 6 (mod 36)
(A218755). Any two terms of either sequence therefore differ by a multiple of 36.

**Evidence.**
- Lean (Mathlib): [`A219543_mathlib.lean`](A219543_mathlib.lean). `A219543_main`, `A218755_main`: any two
  elements of {den B_j : den ≡ 3 (mod 9)} (resp. ≡ 6) differ by a multiple of 36; `bernoulli_den_mod4` from
  Mathlib's von Staudt–Clausen corollaries `Bernoulli.dvd_den_bernoulli`, `Bernoulli.not_sq_dvd_den_bernoulli`.
  Axioms propext, Classical.choice, Quot.sound; zero warnings.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: settled in both entries (Greathouse, 2012). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
