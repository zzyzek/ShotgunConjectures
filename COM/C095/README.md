# Coman C095: P - 80n prime fails for 1105

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 95. Paraphrase: Every Poulet number P has n with P - 80n prime.

**Result.** False: 1105 = 65 (mod 80), so every 1105 - 80n is a multiple of 5 other than 5.

**Argument.** 1105 - 80n = 5 would need 80n = 1100.

**Evidence.**
- Lean: [`C095.lean`](C095.lean) checks 1105 Poulet and no prime 1105 - 80n. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): direct; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Residue obstruction mod 5. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
