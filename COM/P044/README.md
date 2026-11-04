# Coman P044: Carmichael numbers 561 + 272n

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 44. Paraphrase: Are there Carmichael numbers 561 + 272n besides 1105 and 2465?

**Result.** Yes: 75361, 162401, 278545, 340561, ...

**Argument.** Direct.

**Evidence.**
- Lean (Mathlib): [`P044_mathlib.lean`](P044_mathlib.lean) proves the full result (`P044_yes`): 75361, 162401, 278545, 340561 are Carmichael numbers 561 + 272n; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P044.lean`](P044.lean) checks Korselt data and residues. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): list below 10^6; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P044_mathlib.lean`](P044_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P044.lean`](P044.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Further examples 75361, 162401, ... by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
