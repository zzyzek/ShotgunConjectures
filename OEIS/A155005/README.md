# OEIS A155005: a(5+5n) = 1125*10^n for n > 0

**Source.** [A155005](https://oeis.org/A155005), "Smallest number having exactly n divisors that are contained in
its decimal representation" (Reinhard Zumkeller, 2009). "Conjecture: a(5+5n)=1125*10^n for n>0. [Robert G.
Wilson v, Jan 23 2009]" (OEIS text, CC BY-SA 4.0, revision #7, checked 2026-11-06.)

**Reading.** A121041(m) = number of divisors d of m whose decimal string is a contiguous substring of that of m;
a(n) = least m with A121041(m) = n. This reproduces the entry's examples (A121041(110) = 4 etc.).

**Result.** False. It holds for n = 1, 2 (a(10) = 11250, a(15) = 112500, in the entry's data) and fails at n = 3:
A121041(1125000) = 19, so a(20) is not 1125000. The entry's own data list a(19) = 1125000 and a(20) = 3124800.

**Argument.** 1125000 = 2^3 * 3^2 * 5^6 has 84 divisors; exactly 19 of them occur in the string "1125000":
1, 2, 5, 12, 25, 50, 125, 250, 500, 1125, 1250, 2500, 5000, 11250, 12500, 25000, 112500, 125000, 1125000.
Since a(20) has exactly 20 such divisors, a(20) != 1125000. (Numerically A121041(1125*10^k) = 4k + 7 for
k = 2..8, which equals 5k + 5 only at k = 2, so the pattern does not recover later.)

**Evidence.**
- Lean (Mathlib): [`A155005_mathlib.lean`](A155005_mathlib.lean). `A121041 n` = card of divisors d with
  `Nat.digits 10 d <:+: Nat.digits 10 n`; `a n = sInf {m | 0 < m ∧ A121041 m = n}`. Theorems
  `A155005.A121041_1125000 : A121041 1125000 = 19` and `A155005.A155005_conjecture_false : ¬ ∀ n, 0 < n →
  a (5 + 5 * n) = 1125 * 10 ^ n`. The divisor set comes from `Nat.divisors_mul` on 8 * 9 * 125 * 125, and digit
  lists from a fuel-based `digF` proved equal to `Nat.digits 10` (`digF_eq`); finite checks by `decide +kernel`.
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/count.py`](certificate/count.py) ([`count.out`](certificate/count.out)): A121041(1125*10^k) for
  k = 1..8 and A121041(3124800) = 20.
- Outside Lean: none for the disproof. The values a(19) = 1125000, a(20) = 3124800 (minimality) are from the
  entry, not rechecked.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry's own data already contradict the conjecture at a(20) (both added
by the same contributor on the same date); no comment points this out. Not in google-deepmind/formal-conjectures
or otoi-lab/oeis-lean-proofs.
