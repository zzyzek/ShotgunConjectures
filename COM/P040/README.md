# Coman P040: C^2 - 2C - 30k is never prime for C = 162401

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 40. Paraphrase: For every Carmichael number C prime to 15, is some C^2 - 2C - 30k prime? Same question for C1^2 - 2C2 - 30k.

**Result.** No to both: C = 162401 gives C(C-2) = 9 (mod 30), so every positive C^2 - 2C - 30k is a multiple of 3 above 3; likewise 1729^2 - 2*162401 = 9 (mod 30).

**Argument.** 162401 = 2 (mod 3), so C - 2 = 0 (mod 3); and the values are 9 (mod 30), never 3.

**Evidence.**
- Lean (Mathlib): [`P040_mathlib.lean`](P040_mathlib.lean) proves the full result (`P040_no`): C = 162401 (Carmichael, coprime to 15): no C^2 - 2C - 30k is prime; likewise 1729^2 - 2*162401 - 30k; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P040.lean`](P040.lean) checks both 'never prime' statements, 1729 Carmichael (all bases), Korselt data for 162401. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael) for 162401.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): residues; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P040_mathlib.lean`](P040_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P040.lean`](P040.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Mod-3 obstruction for C = 162401; immediate; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement (2026-11-04).
