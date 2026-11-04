# Coman P062: Prime triples p, p + C1 - 1, p + C2 - 1 summing to a Carmichael number

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 62. Paraphrase: Are there other p, C1, C2, C3 with p, p + C1 - 1, p + C2 - 1 prime and sum C3 Carmichael, besides (59, 561, 1729, 2465)?

**Result.** Yes: (1812443, 561, 6601, 5444489).

**Argument.** Direct.

**Evidence.**
- Lean (Mathlib): [`P062_mathlib.lean`](P062_mathlib.lean) proves the full result (`P062_yes`): (1812443, 561, 6601, 5444489) satisfies the conditions (primes by Pratt certificates); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P062.lean`](P062.lean) checks primality of the triple, 561 and 6601 Carmichael (all bases), Korselt data for 5444489. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael) for 5444489.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P062_mathlib.lean`](P062_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P062.lean`](P062.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Further examples (1812443, 561, 6601, 5444489) by search; not found stated. Sources: none found. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search on the witnesses (2026-11-04).
