# Coman C112: Carmichael numbers n(n + a)/(a + 1) (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 112. Paraphrase: Every Carmichael number is n(n + a)/(a + 1) with n, a positive integers.

**Result.** True and trivial: n = C - 1, a = C^2 - 3C + 1 works for every C >= 3.

**Argument.** n(n + a) = (C-1)C(C-2) and a + 1 = (C-1)(C-2).

**Evidence.**
- Lean: [`C112.lean`](C112.lean) checks the identity and exact division for every C >= 3. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): direct; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Explicit identity. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
