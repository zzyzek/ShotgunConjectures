# Coman P065: C = p(q - 2^n) and 5p + 2^n (C124 and C125)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 65. Paraphrase: Study two conjectures: conjecture 124 (3-Carmichael numbers divisible by 5 are p(q - 2^n)) and conjecture 125 (for every odd prime p != 5, infinitely many n with 5p + 2^n prime).

**Result.** The first is true (see C124), the second false (see C125: p = 76739471787787, covering with period 72).

**Argument and evidence.** This item restates [COM-C124](../C124/README.md), [COM-C125](../C125/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C125/C125.lean`](../C125/C125.lean).

**Review level.** `lean-proof` (inherited from [COM-C124](../C124/README.md), [COM-C125](../C125/README.md)).

**Prior art.** Verdict `partly-known`. Restates COM-C124, COM-C125; finding reused from COM-C124 (prior-art agent c1: partly-known), COM-C125 (prior-art agent c1: partly-known). Brief own check: OEIS search on the witness (9890881, 2821+29341, 1024651, 76739471787787) found no entry stating the answer. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, reused search of the restated item(s) (2026-11-04).
