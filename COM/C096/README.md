# Coman C096: P - 150n prime fails for 561

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 96. Paraphrase: Every Poulet number P has n with P - 150n prime.

**Result.** False: 561 = 111 (mod 150), so every 561 - 150n is a multiple of 3 other than 3.

**Argument.** 561 - 150n = 3 would need 150n = 558.

**Evidence.**
- Lean: [`C096.lean`](C096.lean) checks 561 Poulet and no prime 561 - 150n. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): direct; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Residue obstruction mod 3. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
