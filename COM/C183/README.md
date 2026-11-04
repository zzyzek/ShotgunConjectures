# Coman C183: 2^k p n + p^2 for one factor implies all (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 183. Paraphrase: Apart from definable exceptions, if a Poulet number is 2^k p n + p^2 (k >= 0, n an integer) for one prime factor p, then it is 2^k q m + q^2 for every other prime factor q.

**Result.** True and trivial: k = 0 works for every factor (n = P/p - p).

**Argument.** P = p(P/p) = p(P/p - p) + p^2.

**Evidence.**
- Lean: [`C183.lean`](C183.lean) checks the representation for every divisor. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: none

**Review level.** `lean-proof`: the stated result is proved in core Lean (axioms printed by tools/leancheck.sh: propext, Quot.sound, and Classical.choice where `grind` is used).

**Prior art.** Verdict `new` (immediate). Trivial (k = 0, n = P/p - p); not addressed anywhere. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement (2026-11-04).
