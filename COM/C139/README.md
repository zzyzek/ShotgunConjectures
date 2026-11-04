# Coman C139: Primes (q^2 + n)/(n + 1) are bounded

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 139. Paraphrase: For every prime q there are infinitely many primes (q^2 + n)/(n + 1).

**Result.** False: the values are at most q^2.

**Argument.** q^2 + n <= q^2(n + 1).

**Evidence.**
- Lean: [`C139.lean`](C139.lean) checks the bound. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Values bounded by q^2. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
