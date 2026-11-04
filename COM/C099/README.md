# Coman C099: Carmichael 1800n^2 +- 840n +- prime: residue obstruction

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 99. Paraphrase: Every Carmichael number C = 1 (mod 10) not divisible by 3 is 1800n^2 + 840n + p (p prime, 1 mod 30) or 1800n^2 - 840n - q (q prime, 29 mod 30).

**Result.** False: both shapes are 1 (mod 30); 162401 = 11 (mod 30).

**Argument.** 1800 and 840 are multiples of 30; p = 1 and -q = 1 (mod 30).

**Evidence.**
- Lean (Mathlib): [`C099_mathlib.lean`](C099_mathlib.lean) proves the full result (`C099_false`): the negation of the conjecture (n over all integers), witness 162401; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C099.lean`](C099.lean) checks the residue lemmas and 162401's data. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): residues; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C099_mathlib.lean`](C099_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C099.lean`](C099.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Residue obstruction mod 30. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
