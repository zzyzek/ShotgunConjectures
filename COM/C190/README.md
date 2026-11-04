# Coman C190: 2823 is not a sum of three squares

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 190. Paraphrase: Every Carmichael number is a^2 + b^2 + c^2 - 2 with a, b, c prime.

**Result.** False: 2821 + 2 = 2823 = 7 (mod 8) is not a sum of three squares.

**Argument.** Squares are 0, 1, 4 (mod 8).

**Evidence.**
- Lean: [`C190.lean`](C190.lean) checks 2821 Carmichael (all bases) and the mod-8 obstruction. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): direct; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Immediate from squares mod 8 (Legendre three-square obstruction): 2823 = 7 mod 8. Not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement (2026-11-04).
