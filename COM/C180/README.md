# Coman C180: Carmichael numbers in the classes 3, 17, 23, 27 mod 30 exist

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 180. Paraphrase: No Carmichael number is 3, 17, 23 or 27 (mod 30).

**Result.** False: 330794193633 (3), 66243263297 (17), 1097343303233 (23), 28173681537 (27).

**Argument.** Direct computation.

**Evidence.**
- Lean (Mathlib): [`C180_mathlib.lean`](C180_mathlib.lean) proves the full result (`C180_false`): for each r in {3, 17, 23, 27} there is a Carmichael number = r (mod 30); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C180.lean`](C180.lean) checks factor primality, Korselt data, residues. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witnesses; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C180_mathlib.lean`](C180_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C180.lean`](C180.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known`. Wright (2013) proves infinitely many Carmichael numbers = 17 and = 23 (mod 30), which already refutes C180; our explicit witnesses for 3 and 27 (mod 30) are direct computation, not found stated. Sources: [T. Wright, Infinitely many Carmichael numbers in arithmetic progressions, Bull. London Math. Soc. 45 (2013) 943-952](https://arxiv.org/abs/1212.5850): every coprime residue class a mod M contains infinitely many Carmichael numbers; covers 17 and 23 mod 30; [OEIS A258801 (fetched 2026-11-04)](https://oeis.org/A258801): Carmichael numbers divisible by 3 (b-file holds candidates for the classes 3 and 27 mod 30). Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, arXiv/web: Carmichael numbers in arithmetic progressions (Wright 2013, Matomaki, Banks-Pomerance), OEIS A258801, A110889 (2026-11-04).
