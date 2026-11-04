# OEIS A125148: every x coprime to 10 has a prime x + 10m

**Source.** [A125148](https://oeis.org/A125148), comment: "Conjecture: for every odd (prime or nonprime) number x>=1
that is not a multiple of 5 there exists a prime p such that p = z + x; where z is a multiple of 10."
(OEIS text, CC BY-SA 4.0.)

**Result.** True, by Dirichlet's theorem.

**Argument.** gcd(x, 10) = 1, so there are infinitely many primes p ≡ x (mod 10); any such p ≥ x gives
z = p − x, a nonnegative multiple of 10 (positive if one takes p > x, as the entry's terms do).

**Evidence.**
- `certificate/check.py`: x < 10^5.
- Lean (Mathlib): [`A125148_mathlib.lean`](A125148_mathlib.lean), theorem `A125148_conjecture`: every odd x not
  divisible by 5 has z > 0, 10 ∣ z, z + x prime (Dirichlet via `Nat.forall_exists_prime_gt_and_modEq`).
  Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** Verdict known, immediate (OEIS status conjecture; searched 2026-11-04). Direct corollary of Dirichlet's theorem. Sources: [OEIS A125148 (fetched 2026-11-04)](https://oeis.org/A125148): conjecture text unchanged; [Dirichlet's theorem on primes in arithmetic progressions (1837)](https://en.wikipedia.org/wiki/Dirichlet%27s_theorem_on_arithmetic_progressions): infinitely many primes = x (mod 10). Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
