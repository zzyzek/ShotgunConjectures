# Coman C179: Carmichael numbers p^4 + 60p (duplicate of C116)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 179. Paraphrase: Same as conjecture 116: infinitely many Carmichael numbers p^4 + 60p, p prime.

**Result.** False (see C116).

**Argument and evidence.** This item restates [COM-C116](../C116/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C116/C116.lean`](../C116/C116.lean).
Lean (Mathlib): [`C116_mathlib.lean`](../C116/C116_mathlib.lean) (`C116_main, C116_false`) proves the result in full; outside Lean: none.

**Review level.** `lean-proof` (inherited from [COM-C116](../C116/README.md)).

**Prior art.** Verdict `new` (immediate). Restates COM-C116; finding reused from COM-C116 (prior-art agent c1: new). Brief own check: OEIS search on the witness (9890881, 2821+29341, 1024651, 76739471787787) found no entry stating the answer. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, reused search of the restated item(s) (2026-11-04).
