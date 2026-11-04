# Coman C045: Three-term APs of Carmichael numbers without divisibility

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 45. Paraphrase: C1 = (C2 + C3)/2 with Carmichael C1, C2, C3 only if C2 divides both C1 and C3.

**Result.** False: 29341 + 63973 = 2 * 46657. 798 of the 871 three-term APs below 1e13 violate it.

**Argument.** 46657 is divisible by neither 29341 nor 63973.

**Evidence.**
- Lean (Mathlib): [`C045_mathlib.lean`](C045_mathlib.lean) proves the full result (`C045_false`): the negation of the conjecture with (C1, C2, C3) = (46657, 29341, 63973); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C045.lean`](C045.lean) checks factor primality, Korselt data, the AP and non-divisibility. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness and AP count; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C045_mathlib.lean`](C045_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C045.lean`](C045.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). Same counterexample already in the OEIS entry. Sources: [OEIS A214758 (fetched 2026-11-04)](https://oeis.org/A214758): 'Counterexample: 46657 = (29341 + 63973)/2' - Greathouse, Dec 08 2014. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A214758 (2026-11-04).
