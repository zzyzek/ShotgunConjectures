# Coman C088: Only two 2-Poulet numbers with p2 - p1 = 84

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 88. Paraphrase: There are infinitely many 2-Poulet numbers p1 p2 with p2 - p1 = 84.

**Result.** False: the only ones are 3277 = 29 * 113 and 5461 = 43 * 127.

**Argument.** As in C086, ord(2) divides 84 for both primes, so both divide 2^84 - 1 = 3^2 * 5 * 7^2 * 13 * 29 * 43 * 113 * 127 * 337 * 1429 * 5419 * 14449; the pairs 84 apart are (29, 113) and (43, 127), both Poulet.

**Evidence.**
- Lean (Mathlib): [`C088_mathlib.lean`](C088_mathlib.lean) proves the full result (`C088_main, C088_false`): the 2-Poulet numbers p1 p2 with p2 - p1 = 84 are exactly {3277, 5461}, hence finitely many; Fermat + ord_p(2) | N - 1, prime factors of 2^84 - 1 by Pratt certificates. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C088.lean`](C088.lean) checks the identities, the factorization of 2^84 - 1 with certified primes, the pair filter, both Poulet numbers. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Fermat's little theorem / ord_p(2) | p - 1; unique factorization.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): factorization, pairs, and data below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C088_mathlib.lean`](C088_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C088.lean`](C088.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Both primes divide 2^84 - 1; finite check gives 3277, 5461; not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
