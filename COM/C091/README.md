# Coman C091: Carmichael numbers n(a(n-1)+1)(b(n-1)+1): fails for 162401

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 91. Paraphrase: Every Carmichael number is n(an - a + 1)(bn - b + 1) or n(an - a - 1)(bn - b - 1) with n its least prime factor and a, b natural.

**Reading.** a, b >= 1. With a = 0 the first form always holds (C/n = 1 mod n - 1 by Korselt), which would make the statement empty.

**Result.** False: 162401 = 17 * 41 * 233.

**Argument.** The two other factors would be = 1 (resp. -1) mod 16 and >= 17 (resp. 15); the factor pairs of 9553 are (1, 9553) and (41, 233), and 41 = 9 (mod 16).

**Evidence.**
- Lean (Mathlib): [`C091_mathlib.lean`](C091_mathlib.lean) proves the full result (`C091_false`): the negation of the conjecture (n = `Nat.minFac C`, a, b >= 1), witness 162401; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib); factor-pair search from the core file. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C091.lean`](C091.lean) checks factor primality, Korselt data, 17 least prime factor, and the exhaustive factor-pair search for both forms. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C091_mathlib.lean`](C091_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C091.lean`](C091.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 162401 (same as C019) not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
