# Coman C174: Carmichael numbers divisible by 37 and 73 need not have a factor 23 mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 174. Paraphrase: Every Carmichael number divisible by 37 and 73 has a prime factor = 23 (mod 30).

**Result.** False: 294409 = 37 * 73 * 109, factors 7, 13, 19 (mod 30).

**Argument.** Every prime divisor is 37, 73 or 109 (Euclid's lemma in the Lean file).

**Evidence.**
- Lean (Mathlib): [`C173_mathlib.lean`](../C173/C173_mathlib.lean) proves the full result (`C174_false`): the negation of conjecture 174, witness 294409 (every prime factor is 37, 73 or 109); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`../C173/C173.lean`](../C173/C173.lean) (shared with COM-C173) checks (shared with C173) every prime divisor of 294409 is 37, 73 or 109, none 23 mod 30. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- Python check shared with [COM-C173](../C173/certificate/check.py).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C173_mathlib.lean`](../C173/C173_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`../C173/C173.lean`](../C173/C173.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). Same counterexample 294409 = 37*73*109, first term of A182206; its factors are 7, 13, 19 mod 30. Sources: [OEIS A182206 (fetched 2026-11-04)](https://oeis.org/A182206): Coman's entry: Carmichael numbers divisible by 37 and 73; first term 294409 = 37*73*109; Greathouse (2012) notes they are 37*73*(72k+1) by Korselt. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search 294409 (2026-11-04).
