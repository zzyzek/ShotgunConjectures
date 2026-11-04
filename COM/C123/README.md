# Coman C123: Carmichael numbers pq + q - p: fails for 1024651

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 123. Paraphrase: Every Carmichael number is pq + q - p with p, q primes.

**Result.** False: 1024651 = 19 * 199 * 271. 86 of the first 4000 Carmichael numbers fail.

**Argument.** C - 1 = (p+1)(q-1); for each divisor d of 1024650, d - 1 or 1024650/d + 1 is composite.

**Evidence.**
- Lean (Mathlib): [`C123_mathlib.lean`](C123_mathlib.lean) proves the full result (`C123_false, C123_witness`): the negation of the conjecture, witness 1024651; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib); search over divisors of C - 1 from the core file. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C123.lean`](C123.lean) checks Korselt data and the statement for all primes p, q (bounded divisor search). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C123_mathlib.lean`](C123_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C123.lean`](C123.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 1024651 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
