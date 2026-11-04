# Coman C200: No Poulet numbers of the C200 shape for n = 3

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 200. Paraphrase: For every n >= 1 there are infinitely many k >= 1 with 2^(nk)(2^(n(k+1)) + 2^n + 1) + 1 a Poulet number.

**Result.** False: for n = 3 there is no k at all.

**Argument.** The number is (x^(k+1) + 1)(x^k + 1), x = 2^n. For x = 8 = -1 (mod 9), 9 divides it; a psp divisible by 9 would have 6 = ord_9(2) | P - 1, so 3 | P - 1.

**Evidence.**
- Lean: [`C200.lean`](C200.lean) checks the factorization, 9 | P, and P not a psp for every k. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): k < 30; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). For n = 3 the number (8^(k+1)+1)(8^k+1) is divisible by 9, and ord_9(2) = 6 forces 3 | P - 1; a few-line argument not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search for Poulet numbers (2^a+1)(2^b+1) (2026-11-04).
