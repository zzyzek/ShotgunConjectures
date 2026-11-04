# Coman C017: (30n+13)(90n+37)(150n+61) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 17. Paraphrase: The number (30n+13)(90n+37)(150n+61) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 30n+12: t+1, 3t+1, 5t+1; C - 1 = t(15t^2 + 23t + 9), t = 0 (mod 3) and t = 2 (mod 5). So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

**Evidence.**
- Lean (Mathlib): [`C017_mathlib.lean`](C017_mathlib.lean) proves the full result (`C017_main`): for every n, if 30n+13, 90n+37, 150n+61 are prime then the product is a Carmichael number (`Nat.IsCarmichael`); Korselt via Mathlib, polynomial identities by `ring` (tools/family_lean.py). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C017.lean`](C017.lean) checks for every n, each factor minus 1 divides C - 1 (explicit polynomial quotients). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): Korselt divisibility for n < 5000 and first examples; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C017_mathlib.lean`](C017_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C017.lean`](C017.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). Already proved in the OEIS entry. Sources: [OEIS A182133 (fetched 2026-11-04)](https://oeis.org/A182133): Comment states exactly this conjecture (30n+13)(90n+37)(150n+61); 'The conjecture is true (follows from Korselt's criterion)' - Greathouse, Jul 05 2017. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182133, OEIS A182416 (even-n subfamily, also proved by Greathouse 2012) (2026-11-04).
