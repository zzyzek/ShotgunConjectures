# Coman C016: (30n-7)(90n-23)(300n-79) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 16. Paraphrase: The number (30n-7)(90n-23)(300n-79) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 30n-8: t+1, 3t+1, 10t+1; C - 1 = t(30t^2 + 43t + 14), t = 1 (mod 3) and t = 2 (mod 10). So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

**Evidence.**
- Lean (Mathlib): [`C016_mathlib.lean`](C016_mathlib.lean) proves the full result (`C016_main`): for every n, if 30n-7, 90n-23, 300n-79 are prime then the product is a Carmichael number (`Nat.IsCarmichael`); Korselt via Mathlib, polynomial identities by `ring` (tools/family_lean.py). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C016.lean`](C016.lean) checks for every n, each factor minus 1 divides C - 1 (explicit polynomial quotients). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): Korselt divisibility for n < 5000 and first examples; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C016_mathlib.lean`](C016_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C016.lean`](C016.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). One-line Korselt check of the kind Greathouse wrote in sibling entries A182085, A182133; A182132 itself has no proof. Sources: [OEIS A182132 (fetched 2026-11-04)](https://oeis.org/A182132): still states the conjecture; Greathouse 2017 notes only that n = 5 (mod 7) gives a common factor 7. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182132 (2026-11-04).
