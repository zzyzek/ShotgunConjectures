# OEIS A005153: a(n)^(1/n) strictly decreasing — partial result (verified for a(n) <= 10^9)

**Source.** [A005153](https://oeis.org/A005153), practical numbers. Comment (Z.-W. Sun, Jan 12 2013):
"Conjecture: The sequence a(n)^(1/n) (n=3,4,...) is strictly decreasing to the limit 1."
OEIS text, CC BY-SA 4.0, checked 2026-11-07. Listed as research-open in google-deepmind/formal-conjectures
(FormalConjectures/OEIS/5153.lean).

**Result (partial).**
1. *The limit is known.* a(n) = k n log n + O(n log log n) (Weingartner; entry formula), so
   log a(n)/n → 0 and a(n)^(1/n) → 1.
2. *Exact reduction of the monotonicity.* a(n+1)^(1/(n+1)) < a(n)^(1/n) iff
   a(n+1) - a(n) < a(n)(a(n)^(1/n) - 1). Since a(n)/n ~ log a(n)/c with c = 1.33607 (Weingartner), the
   threshold is (1/c)(log a(n))^2 (1 + o(1)) ≈ 0.748 (log x)^2: the conjecture says the gaps between
   consecutive practical numbers near x stay below about 0.748 (log x)^2. This is the practical-number
   analogue of Firoozbakht's conjecture for primes.
3. *Verification.* Strict decrease holds for every n >= 3 with a(n+1) <= 10^9, i.e. for 3 <= n < 64 782 731
   (the b-file has 10^4 terms). The largest ratio of gap to threshold per decade of a(n):
   0.50 (10^3..10^4), 0.51, 0.54, 0.54, 0.57, 0.63 (10^8..10^9, at a(n) = 307 350 504, gap 180).
   The ratio grows slowly with x.

**Method.** Practical numbers <= X enumerated by Stewart's criterion (n = p_1^{e_1}...p_r^{e_r},
p_1 < ... < p_r, is practical iff p_1 = 2 and p_i <= sigma(p_1^{e_1}...p_{i-1}^{e_{i-1}}) + 1) as a
depth-first search over factorizations, sorted, and checked with long double logarithms (smallest margin
(n+1) log a(n) - n log a(n+1) is 0.052 at n = 5, far above rounding error).
Count of practical numbers below 10^9: 64 782 731; a(10000) = 83984 agrees with the b-file.

**Evidence.**
- [`certificate/prac.c`](certificate/prac.c), output [`certificate/prac1e9.out`](certificate/prac1e9.out).
- Lean: none.
- Outside Lean: the computation and items 1-2.

**Obstruction.** The best proven gap bound is far from (log x)^2: Weingartner showed [x - x^0.4872, x] contains
practical numbers. Under a random model with density c/log x the largest gap near x is about (1/c)(log x)^2,
the same leading term as the threshold, so the conjecture is borderline in the same way as Firoozbakht's
(speculation; the rising ratios in item 3 fit it). Details: scan work/OEIS-A005153/REPORT.md.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07: OEIS entry, formal-conjectures (research open), web search on gaps between
practical numbers (best bound x^0.4872, Weingartner). No verification beyond the 10^4-term b-file found.
