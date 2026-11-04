# OEIS A210529: a(n) is defined for every n (Dirichlet)

**Source.** OEIS [A210529](https://oeis.org/A210529): a(n) is 1 or the smallest prime making
|a(n)^2 - prime(n)^2| divisible by all primes below √prime(n). Conjecture: "a(n) is defined for
all positive integers n." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Let p = prime(n) and Q the product of the primes below √p. p is prime to Q (all those
primes are smaller than p). By Dirichlet's theorem there are infinitely many primes a ≡ p (mod Q);
any such a ≠ p gives Q | a - p | a^2 - p^2. So the search in the definition terminates.

**Evidence.** Lean (Mathlib): [`A210529_mathlib.lean`](A210529_mathlib.lean), `A210529_main`: for every prime p and bound m there is a prime a > m, a != p, with every prime l, l^2 < p, dividing a^2 - p^2 (Dirichlet via Mathlib's `Nat.forall_exists_prime_gt_and_modEq`, modulus (p - 1)!). Outside Lean: none (the step from existence to "a smallest such prime exists" is well-foundedness of N). No computation needed.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** Dirichlet's theorem on primes in arithmetic progressions (available in
Mathlib).

**Prior art.** Partly known, immediate. [OEIS A210529](https://oeis.org/A210529) (fetched 2026-11-04) still states the conjecture. The sister [A210708](https://oeis.org/A210708) has E. M. Schmidt's 2013 proof of the non-prime analogue (k = |p - Q|); adding Dirichlet's theorem gives the prime version. Searched: entry, OEIS cross-reference search (A210708, A210721), edit history. Worth an OEIS comment. (Prior-art review 2026-11-04.)
