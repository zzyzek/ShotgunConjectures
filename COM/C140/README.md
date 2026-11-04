# Coman C140: Primes sqrt((q^2 + n)/(n + 1)) are bounded

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 140. Paraphrase: For every prime q there are infinitely many primes p with p^2 = (q^2 + n)/(n + 1).

**Result.** False: p <= q.

**Argument.** p^2 <= q^2.

**Evidence.**
- Lean: [`C140.lean`](C140.lean) checks the bound p <= q. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). p <= q. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
