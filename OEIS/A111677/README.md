# OEIS A111677: "a(n) = 0 iff n ≡ 3 (mod 5)" fails at n = 1

**Source.** [A111677](https://oeis.org/A111677) (offset 1): number of primes of the form "k concatenated with 2n−1"
with k < 2n−1 (row n of [A111676](https://oeis.org/A111676)). Comment: "Conjecture: a(n)=0 iff n== 3 (mod 5).
[Corrected by _R. J. Mathar_, Aug 20 2007]". (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** k runs over 1 ≤ k < 2n−1 and "k concatenated with m" is k·10^d + m, d the number of digits of m. This
reproduces the 29 listed terms (certificate/check.py). Row 1 is empty, as the entry's own a(1) = 0 and the name
("1---> no prime") say.

**Result.** Misstated: a(1) = 0 but 1 ≢ 3 (mod 5). The "if" direction holds for all n: if n ≡ 3 (mod 5) then 2n−1
ends in 5, so every k·10^d + (2n−1) is a multiple of 5 above 5. The remaining direction (a(n) > 0 for n ≥ 2,
n ≢ 3 mod 5) is open; it asks for a prime among k·10^d + m, k < m < 10^d, beyond what Linnik-type bounds give.

**Evidence.**
- Lean (Mathlib): [`A111677_mathlib.lean`](A111677_mathlib.lean): main theorem `A111677_misstated` (the stated
  "iff" fails), `A111677_one`, `A111677_zero_of_mod5`. Check OK, no warnings; axioms propext, Classical.choice,
  Quot.sound.
- certificate/check.py: matches the data; for 2 ≤ n ≤ 100000 with n ≢ 3 (mod 5), a(n) > 0 (sympy isprime).
- Outside Lean: the computational range for the open direction.

**Review level.** `lean-proof` (for the misstatement and the "if" direction).

**Prior art.** Checked 2026-11-06: entry still states the conjecture; not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
