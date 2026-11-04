# Coman C173: Carmichael numbers divisible by 37 and 73 need not be 1 mod 10

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 173. Paraphrase: Every Carmichael number divisible by 37 and 73 is 1 (mod 10).

**Result.** False: 294409 = 37 * 73 * 109 = 9 (mod 10).

**Argument.** Direct computation.

**Evidence.**
- Lean (Mathlib): [`C173_mathlib.lean`](C173_mathlib.lean) proves the full result (`C173_false`): the negation of conjecture 173, witness 294409; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C173.lean`](C173.lean) checks factor primality, Korselt data, residue. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C173_mathlib.lean`](C173_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C173.lean`](C173.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). The counterexample 294409 = 37*73*109 (= 9 mod 10) is the first term of Coman's own OEIS entry A182206 (2012); no source says it refutes C173, but the refutation is reading off the entry. Sources: [OEIS A182206 (fetched 2026-11-04)](https://oeis.org/A182206): Coman's entry: Carmichael numbers divisible by 37 and 73; first term 294409 = 37*73*109; Greathouse (2012) notes they are 37*73*(72k+1) by Korselt; [OEIS A033502 (fetched 2026-11-04)](https://oeis.org/A033502): 294409 is the k = 6 Chernick number (6k+1)(12k+1)(18k+1). Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search 294409, OEIS A352970 (Carmichael numbers ending in 9 lists 294409) (2026-11-04).
