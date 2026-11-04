# Coman C162: Infinitely many Poulet numbers (42m + 1)(42n + 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 162. Paraphrase: There are infinitely many Poulet numbers (42m + 1)(42n + 1).

**Result.** True.

**Argument.** For a prime p = 1 (mod 6), (4^p - 1)/3 = (2^p - 1)((2^p + 1)/3) is a Poulet number (Cipolla) and both factors are 1 (mod 42) (2^p = 2 mod 21 and mod 63); p = 7 gives 5461 = 127 * 43. Infinitely many primes = 1 (mod 6).

**Evidence.**
- Lean (Mathlib): [`C162_mathlib.lean`](C162_mathlib.lean) proves the full result (`C162_main`): the set of base-2 pseudoprimes (42m+1)(42n+1) with m, n >= 1 is infinite; Cipolla (library `cipolla_fermatPsp`) + Mathlib `Nat.exists_prime_gt_modEq_one`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C162.lean`](C162.lean) checks both congruences for every p = 1 (mod 6), the product identity, the instance 5461. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Cipolla's theorem; infinitely many primes = 1 (mod 6).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): p < 200; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C162_mathlib.lean`](C162_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C162.lean`](C162.lean) checks the parts named under Evidence.

**Prior art.** Verdict `partly-known` (immediate). The Cipolla family (4^p-1)/3 is classical; that both factors are 1 mod 42 for p = 1 mod 6 is a two-line congruence not found stated. Sources: [S. Hamahata, Y. Kokubun, Cipolla pseudoprimes, J. Integer Seq. 10 (2007) 07.8.6; OEIS A210454](https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata2/hamahata44.html): (4^p - 1)/3 = (2^p - 1)(2^p + 1)/3 is a base-2 psp for primes p > 3 (Cipolla 1904); the factors' residues mod 42 are not stated. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, OEIS A210454, web: Cipolla pseudoprimes, OEIS A215944 (5461 = 127*43 multiples) (2026-11-04).
