# Coman P103: Poulet numbers (42m+1)(42n+1) (restates C162)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 103. Paraphrase: Study Poulet numbers (42m+1)(42n+1); conjecture 162.

**Result.** True (see C162).

**Argument and evidence.** This item restates [COM-C162](../C162/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C162/C162.lean`](../C162/C162.lean).
Lean (Mathlib): [`C162_mathlib.lean`](../C162/C162_mathlib.lean) (`C162_main`) proves the result in full; outside Lean: none.

**Review level.** `lean-proof` (inherited from [COM-C162](../C162/README.md)).

**Prior art.** Verdict `partly-known` (immediate). Restates COM-C162; finding reused from COM-C162 (this review: partly-known). Sources: [S. Hamahata, Y. Kokubun, Cipolla pseudoprimes, J. Integer Seq. 10 (2007) 07.8.6; OEIS A210454](https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata2/hamahata44.html): (4^p - 1)/3 = (2^p - 1)(2^p + 1)/3 is a base-2 psp for primes p > 3 (Cipolla 1904); the factors' residues mod 42 are not stated. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, reused search of the restated item(s) (2026-11-04).
