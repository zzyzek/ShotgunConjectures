# OEIS A090519: some prime p has floor(10^n/p) prime

**Source.** [A090519](https://oeis.org/A090519) (smallest prime p with floor(10^n/p) prime, 0 if none),
comment: "Conjecture: No term is zero." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** n = 1: floor(10/2) = 5. For n ≥ 2, m = 10^n/4 is an integer and Bertrand's postulate gives a
prime p with m < p ≤ 2m = 10^n/2. Then 2 ≤ 10^n/p < 4, so floor(10^n/p) ∈ {2, 3}, both prime.
(The scan used Nagura's theorem on (x, 6x/5] with p ∈ (10^n/3, 10^n/2]; Bertrand on (10^n/4, 10^n/2] suffices.)

**Evidence.**
- `certificate/check.py`: n = 2..30 with the least prime above 10^n/4.
- Lean (Mathlib): [`A090519_mathlib.lean`](A090519_mathlib.lean), theorem `A090519_conjecture`: for n ≥ 1 some prime
  p has 10^n / p prime (Bertrand via `Nat.exists_prime_lt_and_le_two_mul`). Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** New as a statement; immediate from Bertrand's postulate. [A090519](https://oeis.org/A090519) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
