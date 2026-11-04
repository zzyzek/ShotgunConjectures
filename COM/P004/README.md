# Coman P004: Carmichael numbers 7*13*(18k+1) (restates C089)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 4. Paraphrase: Study Carmichael numbers 91(18k+1); restates conjecture 89 (cofactor 1 or 13 mod 18).

**Result.** False (see C089): 9890881.

**Argument and evidence.** This item restates [COM-C089](../C089/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C089/C089.lean`](../C089/C089.lean).
Lean (Mathlib): [`C089_mathlib.lean`](../C089/C089_mathlib.lean) (`C089_false`) proves the result in full; outside Lean: none.

**Review level.** `lean-proof` (inherited from [COM-C089](../C089/README.md)).

**Prior art.** Verdict `new`. Restates COM-C089; finding reused from COM-C089 (prior-art agent c1: new). Brief own check: OEIS search on the witness (9890881, 2821+29341, 1024651, 76739471787787) found no entry stating the answer. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, reused search of the restated item(s) (2026-11-04).
