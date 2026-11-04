# Coman C013: (30n+7)(60n+13)(150n+31) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 13. Paraphrase: The number (30n+7)(60n+13)(150n+31) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 30n+6: t+1, 2t+1, 5t+1; C - 1 = t(10t^2 + 17t + 8); 2t | C - 1 as t is even, 5t | C - 1 as t = 1 (mod 5). So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

**Evidence.**
- Lean (Mathlib): [`C013_mathlib.lean`](C013_mathlib.lean) proves the full result (`C013_main`): for every n, if 30n+7, 60n+13, 150n+31 are prime then the product is a Carmichael number (`Nat.IsCarmichael`); Korselt via Mathlib, polynomial identities by `ring` (tools/family_lean.py). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C013.lean`](C013.lean) checks for every n, each factor minus 1 divides C - 1 (explicit polynomial quotients). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): Korselt divisibility for n < 5000 and first examples; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C013_mathlib.lean`](C013_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C013.lean`](C013.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). Already proved in the OEIS entry. Sources: [OEIS A182085 (fetched 2026-11-04)](https://oeis.org/A182085): 'The conjecture follows from Korselt's criterion' - Greathouse, Oct 02 2012. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182085 (2026-11-04).
