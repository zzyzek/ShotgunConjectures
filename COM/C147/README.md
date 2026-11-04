# Coman C147: 36(P - d) divisibility for 2-Poulet numbers fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 147. Paraphrase: As C146 for squarefree 2-Poulet numbers.

**Result.** False: 49981 = 151 * 331 (both d fail).

**Argument.** Direct computation.

**Evidence.**
- Lean: [`C147.lean`](C147.lean) checks Poulet property and both failures. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Counterexample 49981 = 151*331 by direct computation; ad hoc divisibility claim; no source mentions it. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS A214305 (2-factor psp) (2026-11-04).
