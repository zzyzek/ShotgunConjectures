# Coman C058: 2-Poulet numbers (q 2^a 3^b 5^c +- 1) 2^n + 1 fail

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 58. Paraphrase: Every 2-Poulet number is (q 2^a 3^b 5^c +- 1) 2^n + 1 with n >= 1, a, b, c >= 0 and q a prime, a prime square or a semiprime.

**Result.** False: 514447 = 359 * 1433.

**Argument.** 514446 = 2 * 257223 forces n = 1. Then q 2^a 3^b 5^c = 257222 = 2 * 7 * 19 * 967 or 257224 = 2^3 * 11 * 37 * 79; in both the part prime to 30 has three prime factors, so q has at least three.

**Evidence.**
- Lean: [`C058.lean`](C058.lean) checks Poulet property, n = 1 forced, the two factorizations with certified primes. Core Lean, no Mathlib, no `native_decide`.
- Lean (Mathlib): [`C058_mathlib.lean`](C058_mathlib.lean) proves `C058_main`: 514447 = 359 · 1433 is a Poulet number with both factors prime, and no q (prime, prime square or product of two primes), a, b, c, n ≥ 1 give 514447 = (q·2^a·3^b·5^c ± 1)·2^n + 1 (n = 1 forced; 7, 19, 967, resp. 11, 37, 79, are prime to 2^a·3^b·5^c and so all divide q). Outside Lean: nothing.
- Outside the core-Lean file: unique factorization (counting prime factors of q; now proved in `C058_mathlib.lean`)
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`C058_mathlib.lean`](C058_mathlib.lean)).

**Prior art.** Verdict `new`. Counterexample 514447 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
