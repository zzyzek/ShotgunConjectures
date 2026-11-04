# Coman P068: Poulet numbers with P1 + P2 - 1 Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 68. Paraphrase: Other Poulet P1, P2 with P1 + P2 - 1 Poulet besides (561, 1905)?

**Result.** Yes: 1105 + 63973 - 1 = 65077 = 59 * 1103.

**Argument.** Direct.

**Evidence.**
- Lean: [`P068.lean`](P068.lean) checks all three Poulet. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Further examples 1105 + 63973 - 1 = 65077 by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
