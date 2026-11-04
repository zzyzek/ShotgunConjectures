# Coman C090: Carmichael numbers divisible by 19 and 37 are 703(18k + 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 90. Paraphrase: Every Carmichael number divisible by 19 and 37 is 703(18k + 1).

**Result.** True (short). In fact the cofactor is 19 (mod 36).

**Argument.** C is odd, so 2^(C-1) = 1 (mod 37) and ord_37(2) = 36 gives 36 | C - 1. 703 = 19 (mod 36) and 19^2 = 1 (mod 36), so C/703 = 19 (mod 36), hence 1 (mod 18). All 701 cases below 1e13 fit.

**Evidence.**
- Lean: [`C090.lean`](C090.lean) checks the statement for every Carmichael number (oddness and the order argument proved in the file). Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): all cases below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Same order argument as Greathouse's notes in A182206/A182515; not found stated for 19, 37. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS search 'divisible by 19 and 37' (2026-11-04).
