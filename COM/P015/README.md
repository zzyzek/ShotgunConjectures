# Coman P015: 2^C mod 560 for Carmichael numbers C

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 15. Paraphrase: Study f = 2^C mod 560 for Carmichael numbers C (Coman notes f = 352 for the first fifteen).

**Result.** Answered: for every integer C >= 4, f = 352 exactly when C = 1 (mod 12). (608 of the 646 Carmichael numbers below 1e9 are 1 mod 12.)

**Argument.** 560 = 16 * 5 * 7. For C >= 4, 2^C = 0 (mod 16); 2^C = 2 (mod 5) iff C = 1 (mod 4) and 2^C = 2 (mod 7) iff C = 1 (mod 3); 352 is 0, 2, 2 modulo 16, 5, 7.

**Evidence.**
- Lean: [`P015.lean`](P015.lean) checks the equivalence for every C >= 4. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): C < 10^4 and Carmichael numbers below 1e9; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Chinese remainder theorem with 560 = 16*5*7; immediate; the characterisation f = 352 iff C = 1 mod 12 not found stated. Sources: [OEIS A110889 (fetched 2026-11-04)](https://oeis.org/A110889): Carmichael numbers not = 1 mod 12 (561, 2465, 8911, ... are the ones with f != 352). Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, Coman3.txt problem 15 wording (Coman skips 561, 2465, 8911, consistent with the answer) (2026-11-04).
