# OEIS A119659: consecutive prime-indexed primes form a triangle from (17, 31, 41) on

**Source.** OEIS [A119659](https://oeis.org/A119659), floor of the area of consecutive prime-indexed-prime
triangles. Comment: "Conjecture: The triples (3,5,11), (5,11,17), (11,17,31) are the only consecutive PIP
triples that cannot form a triangle." (OEIS text, CC BY-SA 4.0.)

**Reading.** q_n = p_{p_n} (A006450: 3, 5, 11, 17, 31, 41, …). (q_n, q_{n+1}, q_{n+2}) forms a
(non-degenerate) triangle iff q_n + q_{n+1} > q_{n+2}, since the sequence is increasing.

**Result.** True: q_n + q_{n+1} > q_{n+2} for every n ≥ 4, and fails exactly for n = 1, 2, 3.

**Argument.** Let m = p_n and M = p_{n+2}.
- n ≤ 62 (p_n ≤ 293): direct computation (`certificate/check.py` checks n ≤ 10⁵).
- n ≥ 63, so m ≥ 307. Nagura (1952): for x ≥ 25 there is a prime in (x, 6x/5), so p_{k+1} < 1.2 p_k when
  p_k ≥ 25, and M < 1.44 m. Rosser–Schoenfeld (1962, (3.13)): p_k < k(ln k + ln ln k) for k ≥ 6; the right
  side increases in k, so q_{n+2} = p_M < 1.44m(ln 1.44m + ln ln 1.44m). Rosser (1938): p_k > k ln k, so
  2q_n = 2p_m > 2m ln m. Finally 2m ln m − 1.44m(ln 1.44m + ln ln 1.44m) = m·h(m) with
  h(m) = 0.56 ln m − 1.44 ln 1.44 − 1.44 ln ln 1.44m; h′(m) > 0 once ln 1.44m > 1.44/0.56, and
  300·h(300) = 21.77 > 0. Hence q_{n+2} < 2q_n < q_n + q_{n+1}.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): the inequality fails only at n = 1, 2, 3 for n ≤ 10⁵; the
  value 300·h(300) and the monotonicity threshold (30-digit mpmath).
- Lean + Mathlib (eventual form only): [`A119659_mathlib.lean`](A119659_mathlib.lean), theorem
  `A119659.A119659_eventually`: q(n+2) < q(n) + q(n+1) for all sufficiently large n. It uses p_{k+1} ≤ 1.1 p_k
  and 0.9 k ln k ≤ p_k ≤ 1.1 k ln k for large k (`pn_pn_plus_one`, `nth_prime_asymp` of the vendored
  PrimeNumberTheoremAnd, `lib/PNTPlus`), so q(n+2) < 2q(n). Axioms: propext, Classical.choice, Quot.sound.
  The threshold is not explicit (the PNT used is ineffective), so this does not cover n ≥ 4.
- The full claim still needs the explicit prime bounds above (Nagura 1952, Rosser–Schoenfeld
  p_k < k(ln k + ln ln k), Rosser p_k > k ln k), the subject of core `core-explicit-prime-bounds-lean`.
- Outside Lean: the explicit threshold n ≥ 63 (the three cited bounds and the real-variable estimate) and the
  finite check for n ≤ 62.

**Review level.** `rechecked` (hand proof from cited bounds plus computation); the eventual form is a Lean
proof (2026-11-07).

**Prior art.** Checked 2026-11-06: still a conjecture in the entry. Bayless, Klyve and Oliveira e Silva,
New bounds and computations on prime-indexed primes, Integers 13 (2013) A43, give PIP bounds but the triangle
claim was not found there or elsewhere by web search. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
