# Coman C150: 12 d1 (P - d2) divisibility fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 150. Paraphrase: For a 3-Poulet number d1 d2 d3 (d1 < d2 < d3): d2^2 - d2 | 12 d1 (P - d2) or P - d3 | 12 d1 (d3^2 - d3).

**Result.** False: 711361 = 7 * 151 * 673.

**Argument.** Direct computation.

**Evidence.**
- Lean: [`C150.lean`](C150.lean) checks Poulet property and both failures. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Counterexample 711361 = 7*151*673 by direct computation; ad hoc divisibility claim; no source mentions it. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS A215672 (2026-11-04).
