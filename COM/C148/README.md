# Coman C148: 360(d2 - 1)/(d1 - 1) is not always an integer

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 148. Paraphrase: For a squarefree 2-Poulet number d1 d2, 360(P - d1)/(d1^2 - d1) = 360(d2^2 - d2)/(P - d2) is a natural number.

**Result.** False: with d1 < d2, 1678541 = 1013 * 1657; for either labeling, 3090091 = 1163 * 2657 (least such). 7157 of 123866 squarefree 2-Poulet numbers below 1e13 fail for both labelings.

**Argument.** Both sides equal 360(d2 - 1)/(d1 - 1). The scan's witness 1678541 passes with the labels swapped (360 * 1012/1656 = 220), so the label-free witness is 3090091.

**Evidence.**
- Lean: [`C148.lean`](C148.lean) checks the identity for the first side, both Poulet numbers, the failures. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witnesses and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Counterexample 3090091 = 1163*2657 (label-free) by direct computation; ad hoc divisibility claim; no source mentions it. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS A214305 (2026-11-04).
