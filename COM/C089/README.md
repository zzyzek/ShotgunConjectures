# Coman C089: Carmichael numbers divisible by 7 and 13: cofactor not always 1 or 13 mod 18

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 89. Paraphrase: Every Carmichael number divisible by 7 and 13 is 91(18k + 1) or 91(18k + 13).

**Result.** False: 9890881 = 7 * 11 * 13 * 41 * 241, cofactor 108691 = 7 (mod 18). 62 failures below 1e13.

**Argument.** Direct computation.

**Evidence.**
- Lean (Mathlib): [`C089_mathlib.lean`](C089_mathlib.lean) proves the full result (`C089_false`): the negation of the conjecture, witness 9890881; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C089.lean`](C089.lean) checks factor primality, Korselt data, the cofactor residue. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C089_mathlib.lean`](C089_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C089.lean`](C089.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 9890881 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS search 'divisible by 7 and 13' Carmichael (2026-11-04).
