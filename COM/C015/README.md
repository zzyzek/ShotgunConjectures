# Coman C015: (330n+7)(660n+13)(990n+19)(1980n+37) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 15. Paraphrase: The number (330n+7)(660n+13)(990n+19)(1980n+37) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 330n+6: t+1, 2t+1, 3t+1, 6t+1; same expansion as C014, 6 | t. So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

**Evidence.**
- Lean (Mathlib): [`C015_mathlib.lean`](C015_mathlib.lean) proves the full result (`C015_main`): for every n, if 330n+7, 660n+13, 990n+19, 1980n+37 are prime then the product is a Carmichael number (`Nat.IsCarmichael`); Korselt via Mathlib, polynomial identities by `ring` (tools/family_lean.py). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C015.lean`](C015.lean) checks for every n, each factor minus 1 divides C - 1 (explicit polynomial quotients). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): Korselt divisibility for n < 5000 and first examples; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C015_mathlib.lean`](C015_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C015.lean`](C015.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). Proved in the OEIS entry; also Chernick's U_4(m) with m = 55n + 1. Sources: [OEIS A182089 (fetched 2026-11-04)](https://oeis.org/A182089): 'The conjecture is true, and can be proved using Korselt's criterion' - Amiram Eldar, Apr 24 2024; [J. Chernick, On Fermat's simple theorem, Bull. AMS 45 (1939) 269-274; statement quoted in OEIS A318646](https://oeis.org/A318646): U_4(m) = (6m+1)(12m+1)(18m+1)(36m+1) is Carmichael when all four factors are prime. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182089 (2026-11-04).
