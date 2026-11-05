# Odd perfect numbers (FAM-odd-perfect)

Famous-problem pilot, problem 6 of 6 (control). Date 2026-11-05. The problem is not settled.

## Statement

Is there an odd perfect number, an odd N with σ(N) = 2N? Lean: `Odd N ∧ N.Perfect` with Mathlib's
`Nat.Perfect` (sum of proper divisors equals N, N > 0), the same as formal-conjectures
`PerfectNumbers.odd_perfect_number_conjecture`. Open.

## Results (all in Lean, `odd_perfect_mathlib.lean`)

Hypotheses throughout: `Odd N`, `N.Perfect`.

| Lean name | Statement |
|---|---|
| `OddPerfect.oddPerfect_mod_four` | N ≡ 1 (mod 4) |
| `OddPerfect.oddPerfect_mod_three` | N ≢ 2 (mod 3) |
| `OddPerfect.oddPerfect_even_exp` | if q is prime, q ≡ 3 (mod 4) and N = q^e M with q ∤ M, then e is even |
| `OddPerfect.oddPerfect_nine_dvd` | 3 ∣ N implies 9 ∣ N |
| `OddPerfect.oddPerfect_touchard` | Touchard (1953): N ≡ 1 (mod 12) or N ≡ 9 (mod 36) |
| `OddPerfect.oddPerfect_not_dvd_105` | Sylvester (1888): 105 ∤ N |
| `OddPerfect.oddPerfect_three_primeFactors` | N has at least 3 distinct prime factors |

Reusable lemmas in the same file: `dvd_sigma_of_pairs` (if every divisor pair d, N/d is distinct
and m ∣ d + N/d, then m ∣ σ(N)), `four_dvd_sigma_odd_pow` (4 ∣ σ(q^(2j+1)) for q ≡ 3 mod 4),
`sigma_split`, `sigma_pow_lower_one/two` (σ(p^k)·p ≥ p^k(p+1), σ(p^k)·p² ≥ p^k(p²+p+1)),
`sigma_mul_prod_pred_le` (σ(N)·∏(p−1) ≤ N·∏p over the prime factors of N, any N ≠ 0).

Axioms (from `tools/leancheck-mathlib.sh`): propext, Classical.choice, Quot.sound for every
theorem. No sorry, no native_decide, zero warnings. Not checked in Lean: nothing beyond the
table; Euler's form is not used and not re-proved.

## Arguments

1. **N ≡ 1 (mod 4).** If N ≡ 3 (mod 4), N is not a square and for every divisor d one of d, N/d is
   1 and the other 3 mod 4, so d + N/d ≡ 0 (mod 4). Pairing d with N/d (`Finset.sum_involution`
   in `ZMod 4`) gives 4 ∣ σ(N) = 2N, contradicting N odd.
2. **N ≢ 2 (mod 3).** Same pairing mod 3 (squares are 0, 1 mod 3): 3 ∣ 2N, so 3 ∣ N.
3. **Even exponent for q ≡ 3 (mod 4).** σ(q^(2j+1)) = (1 + q)(1 + q² + … + q^(2j)), so 4 ∣ σ(q^e)
   for odd e; σ(q^e) ∣ σ(N) = 2N gives 4 ∣ 2N.
4. **9 ∣ N.** 3 ≡ 3 (mod 4), so the exponent of 3 is even and positive.
5. **Touchard.** Combine 1, 2, 4.
6. **105.** Write N = 3^a 5^b 7^c M with M coprime to 105. By 3, a and c are even and positive,
   so a, c ≥ 2; b ≥ 1. Then 2N = σ(N) ≥ σ(3^a)σ(5^b)σ(7^c)M and
   σ(3^a)/3^a ≥ 13/9, σ(5^b)/5^b ≥ 6/5, σ(7^c)/7^c ≥ 57/49, product 4446/2205 > 2.
7. **Three prime factors.** σ(p^k)(p − 1) < p^(k+1), so 2∏(p − 1) ≤ ∏p over the prime factors.
   No prime is 2. One prime p ≥ 3: 2(p − 1) > p. Two distinct odd primes p < q (q ≥ 5):
   2(p − 1)(q − 1) > pq. Zero primes: N = 1, σ(1) = 1.

## Outside Lean

certificate/sigma_power_targets.py`: σ(p^a) = q^j for p ≠ q in {3, 5, 7, 11, 13}, a ≤ 400. Only
σ(3^2) = 13 and σ(3^4) = 11². Used for the obstacle log, not for any theorem.

## Obstacles (where it stops)

* **Sylvester's 4 distinct prime factors.** The abundancy bound (lemma 7 with three primes)
  leaves the prime sets {3, 5, 7}, {3, 5, 11}, {3, 5, 13}. {3, 5, 7} is excluded by the 105
  theorem. For {3, 5, 11} and {3, 5, 13} the interval of possible abundancies straddles 2
  ((3/2)(5/4)(11/10) = 2.0625, (3/2)(5/4)(13/12) = 2.03), so inequalities alone cannot finish.
  The classical proof goes into the exponents: e.g. with a ≥ 4 the odd number σ(3^a) must be a
  product of 5s and 11s, which is the S-unit equation (3^(a+1) − 1)/2 = 5^x 11^y; then the same
  for σ(5^b), σ(11^c). Each such equation needs an argument valid for all exponents
  (multiplicative orders plus a congruence sieve, or Zsigmondy/Bang primitive prime divisors).
  Mathlib has orders and `ZMod`, but no Zsigmondy theorem and no S-unit machinery, so each case
  would be a hand-built sieve. Not attempted within the time box.
* **Euler's form (p ≡ α ≡ 1 mod 4 for the special prime).** Already proved by AlphaProof in the
  formal-conjectures fork (link in FC `PerfectNumbers.lean`); not redone. Theorem 3 above is the
  part of it that the 105 proof needs.
* **Ochem–Rao (N > 10^1500, ≥ 101 prime factors with multiplicity).** FC states it with sorry.
  It rests on a factor-chain search with huge factorizations; out of reach for a kernel
  certificate (same obstacle class as the Wieferich 2^3510 − 1 factorization in this pilot).
* **Finiteness for a fixed number K of prime factors** (Dickson 1913; Nielsen: N < 2^(4^K)).
  Same shape as the Lehmer bound proved in this pilot (`work/famous/lehmer`) and as
  core-multiplicative-exact-target (σ(N)/N = 2 is an exact rational target for a multiplicative
  function); not attempted here.

## Literature and formalisation checked (2026-11-05)

* formal-conjectures `FormalConjectures/Wikipedia/PerfectNumbers.lean` (main branch, fetched
  2026-11-05): states the conjecture (open), Ochem–Rao (solved, sorry) and Euler's form (solved,
  formal proof by AlphaProof in fork mzhorvath1/formal-conjectures @7deed78). No Touchard, 105 or
  prime-count statements. `FormalConjecturesForMathlib/NumberTheory/PerfectNumber.lean` only
  defines iterated perfect numbers.
* Mathlib: `Nat.Perfect`, `Nat.perfect_iff_sum_divisors_eq_two_mul`, σ multiplicativity; the
  Euclid–Euler theorem for even perfect numbers is in Mathlib's Archive. No odd-perfect results.
* OpenAI math repository (`~/claude/openai-math/repo`, CONTENTS.md and `lean/`): no item on
  perfect numbers.
* Web search: no Lean formalisation of Touchard, 105 or the prime-count bound found. A Zenodo
  preprint (January 2026, github AEjonanonymous/OPN) claims a Lean-checked non-existence proof
  for Euler-form N with special prime p ≥ 5; not read, unverified, not used.
* Sources for the mathematics: Touchard (1953), Holdener's short proof (2002), Sylvester (1888);
  Starni, arXiv:1709.05286 (extensions of Touchard).

## New or known

All results are classical (Euler, Sylvester 1888, Touchard 1953). As far as the checks above go,
these are the first Lean proofs of Touchard's congruence, 105 ∤ N and ω(N) ≥ 3 for odd perfect N.
