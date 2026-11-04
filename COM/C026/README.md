# Coman C026: 360ab + 1 = c^2 does not give Carmichael multiples of ab

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 26. Paraphrase: If a, b are prime and 360ab + 1 = c^2 with c prime, then infinitely many Carmichael numbers have the form abd.

**Result.** False: (a, b, c) = (2, 7, 71) and (3, 67, 269) satisfy the hypothesis and no Carmichael number is divisible by 14 or by 201.

**Argument.** Carmichael numbers are odd, so 14 never divides one. If 201 = 3 * 67 divides a Carmichael number C, then
C is odd, so 2^(C-1) = 1 (mod 67); ord_67(2) = 66 gives 66 | C - 1, so 3 | C - 1, contradicting 3 | C.
More generally a, b = 90a + 1, c = 180a + 1 all prime gives 360ab + 1 = c^2 and a | b - 1 blocks every
Carmichael multiple (a = 3, 13, 17, 31, 37, 47, ...). With a, b odd, distinct and neither dividing the
other minus one, Larsen's theorem gives infinitely many Carmichael multiples (corrected form; see the
scan note).

**Evidence.**
- Lean: [`C026.lean`](C026.lean) checks the hypotheses, Carmichael numbers are odd, and no Carmichael number is divisible by 201. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none for the counterexamples
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): hypotheses, the family a, 90a+1, 180a+1, and no Carmichael multiple of 201 below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Carmichael numbers are odd; 201 case by Korselt. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
