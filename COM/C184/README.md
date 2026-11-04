# Coman C184: P - 5 is a sum of distinct powers of 2 (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 184. Paraphrase: For every Poulet number P, P - 5 is a sum of distinct powers of 2.

**Result.** True and trivial: binary expansion of the positive integer P - 5.

**Argument.** Every positive integer has a binary expansion.

**Evidence.**
- Lean (Mathlib): [`C184_mathlib.lean`](C184_mathlib.lean) proves `C184_main`: every Poulet number P (Mathlib `Nat.FermatPsp P 2`) has 5 < P and P - 5 = ∑_{i ∈ S} 2^i for a finite set S (its binary digit positions, Mathlib `Nat.bitIndices`). Outside Lean: nothing.
- Outside Lean: none (standard)

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib ([`C184_mathlib.lean`](C184_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`).

**Prior art.** Verdict `new` (immediate). Binary expansion of P - 5; trivial; not addressed anywhere. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement (2026-11-04).
