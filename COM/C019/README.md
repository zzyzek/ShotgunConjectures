# Coman C019: 3-Carmichael factor pattern d1(n+1) - n fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 19. Paraphrase: For every 3-Carmichael number d1 d2 d3 (d1 < d2 < d3) either d2 and d3 are both d1(n+1) - n, or both d1 n - (n+1) (n natural).

**Result.** False. Counterexample 162401 = 17 * 41 * 233 (41 = 233 = 9 mod 16). 637 failures below 1e13.

**Argument.** The two patterns say d2, d3 = 1 or -1 modulo d1 - 1; 41 is 9 mod 16.

**Evidence.**
- Lean (Mathlib): [`C019_mathlib.lean`](C019_mathlib.lean) proves the full result (`C019_false`): the negation of the conjecture (each of d2, d3 with its own n), witness 162401; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C019.lean`](C019.lean) checks factor primality, Korselt data, and that 41 is neither 17(n+1) - n nor 17n - (n+1). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C019_mathlib.lean`](C019_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C019.lean`](C019.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 162401 not found stated; same counterexample as C091. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
