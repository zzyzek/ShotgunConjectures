# Coman C014: (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 14. Paraphrase: The number (30n-29)(60n-59)(90n-89)(180n-179) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: u = 30(n-1): u+1, 2u+1, 3u+1, 6u+1; C - 1 = u(36u^3 + 72u^2 + 47u + 12), divisible by 6u as 6 | u. So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

**Evidence.**
- Lean (Mathlib): [`C014_mathlib.lean`](C014_mathlib.lean) proves the full result (`C014_main`): for every n, if 30n-29, 60n-59, 90n-89, 180n-179 are prime then the product is a Carmichael number (`Nat.IsCarmichael`); Korselt via Mathlib, polynomial identities by `ring` (tools/family_lean.py). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C014.lean`](C014.lean) checks for every n, each factor minus 1 divides C - 1 (explicit polynomial quotients). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): Korselt divisibility for n < 5000 and first examples; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C014_mathlib.lean`](C014_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C014.lean`](C014.lean) checks the parts named under Evidence.

**Prior art.** Verdict `known` (immediate). With m = 5(n-1) the factors are 6m+1, 12m+1, 18m+1, 36m+1, Chernick's U_4(m) (1939); A182088 still lists it as a conjecture, so an OEIS comment is worth adding. Sources: [J. Chernick, On Fermat's simple theorem, Bull. AMS 45 (1939) 269-274; statement quoted in OEIS A318646](https://oeis.org/A318646): U_4(m) = (6m+1)(12m+1)(18m+1)(36m+1) is Carmichael when all four factors are prime; [OEIS A182088 (fetched 2026-11-04)](https://oeis.org/A182088): still states the conjecture; no proof note. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182088, OEIS A318646 (Chernick universal forms) (2026-11-04).
