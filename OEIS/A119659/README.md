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
- Lean: none. `lean_status: needs-mathlib`; missing pieces are the explicit prime bounds above (Nagura 1952,
  Rosser–Schoenfeld p_k < k(ln k + ln ln k), Rosser p_k > k ln k), the subject of core
  `core-explicit-prime-bounds-lean`.
- Outside Lean: everything (the three cited bounds, the finite check, the real-variable estimate).

**Review level.** `rechecked` (hand proof from cited bounds plus computation).

**Prior art.** Checked 2026-11-06: still a conjecture in the entry. Bayless, Klyve and Oliveira e Silva,
New bounds and computations on prime-indexed primes, Integers 13 (2013) A43, give PIP bounds but the triangle
claim was not found there or elsewhere by web search. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
