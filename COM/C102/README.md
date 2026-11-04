# Coman C102: Odd Poulet numbers are (a^2 - b^2)/8 (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 102. Paraphrase: Every Poulet number ending in 1, 5 or 9 is (a^2 - b^2)/8 with a, b positive integers.

**Result.** True and trivial: a = 2P + 1, b = 2P - 1 works for every P >= 1.

**Argument.** (2P+1)^2 - (2P-1)^2 = 8P.

**Evidence.**
- Lean: [`C102.lean`](C102.lean) checks the identity for every P >= 1. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): direct; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Identity (2P+1)^2 - (2P-1)^2 = 8P. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
