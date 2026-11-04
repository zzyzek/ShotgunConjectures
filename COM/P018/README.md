# Coman P018: Carmichael triples p(C1 - 1) - C2 = C3

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 18. Paraphrase: Are there Carmichael triples with p(C1 - 1) - C2 = C3, p prime, besides (561, 1729, 8911)?

**Result.** Yes: 14293 * 560 - 8911 = 7995169 = 7 * 13 * 103 * 853, with (C1, C2, C3) = (561, 8911, 7995169).

**Argument.** Direct.

**Evidence.**
- Lean (Mathlib): [`P018_mathlib.lean`](P018_mathlib.lean) proves the full result (`P018_yes`): a prime p and Carmichael C1, C2, C3 with p(C1-1) - C2 = C3 other than (561, 1729, 8911): (14293; 561, 8911, 7995169); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P018.lean`](P018.lean) checks the identity, 14293 prime, 561 Carmichael, Korselt data. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael) for 8911 and 7995169.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P018_mathlib.lean`](P018_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P018.lean`](P018.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Further examples (561, 8911, 7995169) with p = 14293 by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
