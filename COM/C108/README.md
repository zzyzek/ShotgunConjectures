# Coman C108: Carmichael numbers n(n + p)/8 with p a prime power: fails for 162401

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 108. Paraphrase: Every Carmichael number is n(n + p)/8 with n >= 1 and p a prime or a prime power.

**Result.** False: 162401. 363 of the first 3000 Carmichael numbers fail.

**Argument.** 8C = n(n + p) needs n | 8C and n < sqrt(8C); for each of the 16 such divisors the cofactor 8C/n - n has two distinct prime factors.

**Evidence.**
- Lean (Mathlib): [`C108_mathlib.lean`](C108_mathlib.lean) proves the full result (`C108_false`): the negation of the conjecture (8C = n(n+p), p a Mathlib `IsPrimePow`), witness 162401; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib); divisor search from the core file. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C108.lean`](C108.lean) checks Korselt data and the exhaustive divisor search with two certified primes per candidate (prime powers defined in the file). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C108_mathlib.lean`](C108_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C108.lean`](C108.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 162401 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
