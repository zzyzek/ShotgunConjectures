# Coman P133: P - 5 as a sum of powers of 2 (restates C184)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 133. Paraphrase: Study conjecture 184.

**Result.** True and trivial (see C184).

**Argument and evidence.** This item restates [COM-C184](../C184/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean (Mathlib): [`P133_mathlib.lean`](P133_mathlib.lean) (same proof as COM-C184's `C184_mathlib.lean`): `P133_main`, every Poulet number P has 5 < P and P - 5 = ∑_{i ∈ S} 2^i for a finite set S. Outside Lean: nothing.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`P133_mathlib.lean`](P133_mathlib.lean)).

**Prior art.** Verdict `new` (immediate). Restates COM-C184; finding reused from COM-C184 (this review: new). Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, reused search of the restated item(s) (2026-11-04).
