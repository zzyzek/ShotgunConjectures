# Coman C151: Carmichael numbers divisible by 8911 are 8911(198n + 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 151. Paraphrase: Every Carmichael number divisible by 8911 is 8911(198n + 1).

**Result.** True (short; holds for every Poulet number divisible by 8911).

**Argument.** ord_19(2) = 18 and ord_67(2) = 66 give 198 | C - 1; 8911 = 1 (mod 198). All 250 Poulet multiples of 8911 below 1e13 fit.

**Evidence.**
- Lean: [`C151.lean`](C151.lean) checks the statement for every base-2 psp and every Carmichael number. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): data below 1e13; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Immediate from Korselt (ord_19(2), ord_67(2)); the same argument is Greathouse's 2012 note in A182206 for 37*73, but no source states it for 8911. Sources: [OEIS A182206 (fetched 2026-11-04)](https://oeis.org/A182206): Coman's entry: Carmichael numbers divisible by 37 and 73; first term 294409 = 37*73*109; Greathouse (2012) notes they are 37*73*(72k+1) by Korselt. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search 8911 198, OEIS A214758, A212920 (2026-11-04).
