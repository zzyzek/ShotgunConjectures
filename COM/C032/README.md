# Coman C032: Exceptions are not only 5461(42k - 13)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 32. Paraphrase: The Poulet numbers divisible by a smaller Poulet number and not of the form p((m+1)p - m)((n+1)p - n) are exactly multiples 5461(42k - 13).

**Reading.** p is taken to be a prime factor of the Poulet number (for 3048841, with three prime factors, any factorization into three factors >= 2 uses the three primes, so nothing changes).

**Result.** False: 3048841 = 61 * 151 * 331 is divisible by the Poulet number 49981 = 151 * 331, is not of the form, and is not a multiple of 5461.

**Argument.** For p = 61 the cofactors are 31 mod 60; for p = 151 and 331 the cofactor 61 is not 1 mod p - 1.

**Evidence.**
- Lean: [`C032.lean`](C032.lean) checks both Poulet numbers, the divisibilities, and the exhaustive form check for p = 61, 151, 331. Core Lean, no Mathlib, no `native_decide`.
- Lean (Mathlib): [`C032_mathlib.lean`](C032_mathlib.lean) proves `C032_main` / `C032_false`: 3048841 and 49981 are Poulet numbers (Mathlib `Nat.FermatPsp`), 49981 ∣ 3048841, 5461 ∤ 3048841, and 3048841 ≠ p((m+1)p - m)((n+1)p - n) for all natural p, m, n (not only prime p: p³ ≤ 3048841 and p ∣ 3048841 leave p = 61, then 49981 = (60m+61)(60n+61) has no solution). So the reading below is not needed. Outside Lean: nothing.
- Outside the core-Lean file: the reading that p ranges over the prime factors (removed by `C032_mathlib.lean`)
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: proved in Lean + Mathlib for every natural p ([`C032_mathlib.lean`](C032_mathlib.lean)).

**Prior art.** Verdict `new`. Counterexample 3048841 not found stated; A215944 still lists the conjecture. Sources: [OEIS A215944 (fetched 2026-11-04)](https://oeis.org/A215944): still states the conjecture, checked for small cases; no counterexample; [OEIS A050217 (fetched 2026-11-04)](https://oeis.org/A050217): contains 3048841 as data only. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A215944, OEIS search 3048841 (2026-11-04).
