# Coman P069: Poulet numbers with P1 + rev(P2) - 2 Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 69. Paraphrase: Other Poulet P1, P2 with P1 + rev(P2) - 2 Poulet besides (561, 645)?

**Result.** Yes: 341 + rev(249841) - 2 = 341 + 148942 - 2 = 149281.

**Argument.** Direct.

**Evidence.**
- Lean: [`P069.lean`](P069.lean) checks all three Poulet and the sum. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Further examples 341 + 148942 - 2 = 149281 by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
