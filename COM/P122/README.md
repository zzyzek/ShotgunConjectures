# Coman P122: Carmichael and Poulet numbers p + q + r with primes in one class

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 122. Paraphrase: Other Carmichael or Poulet numbers p + q + r with p, q, r prime in the same class coprime to 30, besides 561 = 47 + 167 + 347?

**Result.** Yes: Poulet 4371 = 7 + 7 + 4357 and Carmichael 656601 = 7 + 7 + 656587. Such sums are 3r (mod 30), so only numbers = 3, 9, 21, 27 (mod 30) can qualify.

**Argument.** Direct.

**Evidence.**
- Lean (Mathlib): [`P122_mathlib.lean`](P122_mathlib.lean) proves the full result (`P122_yes`): 4371 = 7 + 7 + 4357 is a base-2 pseudoprime (`Nat.FermatPsp`), 656601 = 7 + 7 + 656587 is Carmichael, and such sums are 3c (mod 30); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P122.lean`](P122.lean) checks the sums, primality, 4371 Poulet, Korselt data for 656601, the residue lemma. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael) for 656601.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): search below 10^6; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P122_mathlib.lean`](P122_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P122.lean`](P122.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Further examples 4371 = 7+7+4357 and 656601 = 7+7+656587 by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
