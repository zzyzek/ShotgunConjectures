# Coman C194: x(P1 - 1) = y(P2 - 1) has other solutions (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 194. Paraphrase: For Poulet numbers P1, P2 sharing a prime factor, x(P1 - 1) = y(P2 - 1) has integer solutions other than x = P2 - 1, y = P1 - 1.

**Result.** True and trivial: (2(P2 - 1), 2(P1 - 1)), or (0, 0).

**Argument.** Scale the trivial solution.

**Evidence.**
- Lean: [`C194.lean`](C194.lean) checks the doubled solution. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Scaling the trivial solution; trivial. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement (2026-11-04).
