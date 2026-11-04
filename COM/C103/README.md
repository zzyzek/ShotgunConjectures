# Coman C103: Digital root and prime factors of Carmichael numbers: fails for 62745

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 103. Paraphrase: If a Carmichael number C is not Harshad and its digital root s is not 1, then every prime factor d != 3 is n(s-1) +- 1 with n >= 1.

**Result.** False: 62745 = 3 * 5 * 47 * 89 (s = 6, d = 5). 79 failures (scan).

**Argument.** Digit sum 24 does not divide 62745; 5 = 5n +- 1 has no solution.

**Evidence.**
- Lean (Mathlib): [`C103_mathlib.lean`](C103_mathlib.lean) proves the full result (`C103_false`): the negation of the conjecture (digit sum via `Nat.digits`, digital root 1 + (C-1) % 9), witness 62745; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C103.lean`](C103.lean) checks factor primality, Korselt data, digit facts, the failed form. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C103_mathlib.lean`](C103_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C103.lean`](C103.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 62745 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
