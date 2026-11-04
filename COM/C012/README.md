# Coman C012: Digit-sum relations for Carmichael numbers with all factors 6k+1

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 12. Paraphrase: Every Carmichael number C with all prime factors = 1 (mod 6) satisfies one of: (1) C is Harshad; (2) n s(C) - n + 1 divides C for some integer n; (3) s((C+1)/2) divides C; (4) n s((C+1)/2) - n + 1 divides C; (5) s(C) = s((C+1)/2) (s = digit sum).

**Reading.** n = 0 in (2) or (4) gives the divisor 1 and makes the conjecture empty, so n != 0 (n of either sign).

**Result.** False. Counterexample 405739681 = 229 * 457 * 3877.

**Argument.** s(C) = 43, s((C+1)/2) = 40. 43 and 40 do not divide C. A divisor |n*42 + 1| (resp. |n*39 + 1|) with n != 0
is a divisor > 1 that is +-1 modulo 42 (resp. 39); none of the 7 divisors > 1 of C is.

**Evidence.**
- Lean (Mathlib): [`C012_mathlib.lean`](C012_mathlib.lean) proves the full result (`C012_false`): the negation of the conjecture (digit sums via `Nat.digits`, integer n != 0), witness 405739681; every divisor is a sub-product of the factorization (library `mem_divisorsList_of_dvd`); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C012.lean`](C012.lean) checks factor primality, Korselt data, digit sums, and the five relations on the divisor list. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael); that the subset products are all divisors (unique factorization).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): witness check; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C012_mathlib.lean`](C012_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C012.lean`](C012.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample 405739681 not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, no matching OEIS entry among Coman's 60 OEIS entries (2026-11-04).
