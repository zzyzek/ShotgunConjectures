# Coman C137: Primes (P + n)/(n + 1) are bounded

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 137. Paraphrase: For every Poulet number P there are infinitely many primes (P + n)/(n + 1).

**Result.** False: the values are at most P.

**Argument.** P + n <= P(n + 1).

**Evidence.**
- Lean: [`C137.lean`](C137.lean) checks the bound. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Values bounded by P. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
