# Coman C149: The C148 relation fails for a base-3 psp

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 149. Paraphrase: As C148 for every two-factor squarefree Fermat pseudoprime to any base.

**Result.** False: 1241143 = 547 * 2269 is a base-3 psp and fails for either labeling.

**Argument.** Direct computation.

**Evidence.**
- Lean: [`C149.lean`](C149.lean) checks base-3 psp property and failures. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Counterexample 1241143 = 547*2269 (base 3) by direct computation; ad hoc divisibility claim; no source mentions it. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS A214305, OEIS search for the witness (2026-11-04).
