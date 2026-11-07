# OEIS A103152: a(23) = 725 is not divisible by 3

**Source.** [A103152](https://oeis.org/A103152) (Lei Zhou, 2005): smallest odd number that is 2p + q (p, q odd
primes) in exactly n ways. Comment: "Conjecture: except for the 2nd, 3rd and 4th terms, all other terms are
divisible by 3". Later comments in the same entry: "a(23)=725 is also not divisible by 3" (D. S. McNeil,
Sep 06 2010) and "The only terms a(n) not divisible by 3 for n <= 1450 are a(2),a(3),a(4) and a(23)" (Robert
Israel, Mar 17 2020). (OEIS text checked 2026-11-06.)

**Result.** False, already refuted in the entry: a(23) = 725 = 5^2 * 29.

**Argument.** 725 has exactly 23 representations 2p + q with p, q odd primes, and every odd m < 725 has a
different number of representations; so a(23) = 725, and 3 does not divide 725.

**Evidence.**
- Lean (Mathlib): [`A103152_mathlib.lean`](A103152_mathlib.lean). `reps m` counts odd primes p with m - 2p an odd
  prime >= 3 (Mathlib `Nat.Prime`). Main theorem `A103152_23 : reps 725 = 23 ∧ ∀ m < 725, m % 2 = 1 → reps m ≠ 23`,
  plus `A103152_23_not_dvd_three`. Primality below 726 is reduced to an explicit list (members by `norm_num`,
  non-members by a divisor among 2..23) and the counts are evaluated with `decide +kernel` (kernel reduction;
  no `native_decide`). Check `tools/leancheck-mathlib.sh`: OK (about 55 s), no warnings, axioms within propext,
  Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): a(1..24) = 9, 13, 17, 29, ..., 725, 393 (matches the data).
- Outside Lean: none.

**Review level.** `lean-witness`.

**Prior art.** Known: McNeil 2010 and Israel 2020 comments in the entry itself (the conjecture text was never
removed). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
