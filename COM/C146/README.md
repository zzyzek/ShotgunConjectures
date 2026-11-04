# Coman C146: 36(P - d) divisibility for 3-Poulet numbers fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 146. Paraphrase: For every 3-Poulet number P and each prime factor d: d^2 - d | 36(P - d) or P - d | 36(d^2 - d).

**Result.** False: 149281 = 11 * 41 * 331 (d = 331). 14029 failures below 1e13.

**Argument.** Direct computation.

**Evidence.**
- Lean: [`C146.lean`](C146.lean) checks Poulet property, factors, the failure at d = 331. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Counterexample 149281 = 11*41*331 by direct computation; ad hoc divisibility claim; no source mentions it. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS A215672 (3-factor psp) (2026-11-04).
