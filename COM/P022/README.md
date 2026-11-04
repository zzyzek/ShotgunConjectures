# Coman P022: Carmichael numbers 176n + 1

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 22. Paraphrase: Are there Carmichael numbers 176n + 1 besides 2465 and 15841?

**Result.** Yes: 340561, 670033, 825265, 1615681, ... (15 below 10^7).

**Argument.** Direct.

**Evidence.**
- Lean (Mathlib): [`P022_mathlib.lean`](P022_mathlib.lean) proves the full result (`P022_yes`): 340561, 670033, 825265, 1615681 are Carmichael numbers 176n + 1; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P022.lean`](P022.lean) checks Korselt data and residues for the first three. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): list below 10^7; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P022_mathlib.lean`](P022_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P022.lean`](P022.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Further examples 340561, 670033, ... (Carmichael numbers = 1 mod 176) by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
