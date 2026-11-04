# Coman P016: Carmichael numbers 1 mod 10, 12 or 14: fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 16. Paraphrase: Study the conjecture that every Carmichael number is 1 (mod 10), 1 (mod 12) or 1 (mod 14).

**Result.** False: 62745 = 3 * 5 * 47 * 89 is 5, 9, 11 modulo 10, 12, 14.

**Argument.** Direct.

**Evidence.**
- Lean (Mathlib): [`P016_mathlib.lean`](P016_mathlib.lean) proves the full result (`P016_false`): 62745 is Carmichael and = 5, 9, 11 modulo 10, 12, 14; Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`P016.lean`](P016.lean) checks Korselt data and residues. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`P016_mathlib.lean`](P016_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`P016.lean`](P016.lean) checks the parts named under Evidence.

**Prior art.** Verdict `partly-known` (immediate). 62745 appears in A110889 and A258801; that it is also not 1 mod 10 or mod 14 (hence refutes the conjecture) is read off directly; no source states the refutation. Sources: [OEIS A110889 (fetched 2026-11-04)](https://oeis.org/A110889): lists 62745 among Carmichael numbers not = 1 mod 12; [OEIS A258801 (fetched 2026-11-04)](https://oeis.org/A258801): 62745 = 3*5*47*89 is the second Carmichael number divisible by 3. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS search 62745 (2026-11-04).
