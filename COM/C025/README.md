# Coman C025: Not every prime is (Cq - 1)/(q - 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 25. Paraphrase: Every prime p can be written (Cq - 1)/(q - 1) with C a Carmichael number and q prime.

**Result.** False: no prime below 561 (e.g. p = 2) has this form.

**Argument.** (Cq - 1)/(q - 1) = C + (C - 1)/(q - 1) >= C >= 561, the least Carmichael number.

**Evidence.**
- Lean: [`C025.lean`](C025.lean) checks every Carmichael number is >= 561 (exhaustive check of all n < 561 and all bases) and (Cq - 1)/(q - 1) >= C, so the value 2 is impossible. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Value is at least the least Carmichael number 561. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
