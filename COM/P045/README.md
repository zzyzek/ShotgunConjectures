# Coman P045: Carmichael numbers C = n(C - 1) - p(p + 2)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 45. Paraphrase: Are there Carmichael numbers C = n(C-1) - p(p+2) (p, p+2 twin primes) besides 1729?

**Result.** Yes: 6601 = 67 * 6600 - 659 * 661 (scan: one exists for each of the first 200 Carmichael numbers).

**Argument.** Direct.

**Evidence.**
- Lean: [`P045.lean`](P045.lean) checks 6601 Carmichael (all bases), 659 and 661 prime, the identity. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Further examples 6601 = 67*6600 - 659*661 by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
