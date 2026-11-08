# OEIS A181674: the average order is 1, not Theta(log log n)

**Source.** [A181674](https://oeis.org/A181674), number of ways to write n = P + m with P a primorial (A002110,
1 included, per the example 10 = 1 + 9) and m a semiprime. Comment: "Conjecture: Average order is
Theta(log log n). - Charles R Greathouse IV, May 25 2011" (OEIS text, CC BY-SA 4.0, revision #11 of Mar 09 2022,
checked 2026-11-07, history read).

**Reading.** Average order: M(x) = (1/x) sum_{n<=x} a(n).

**Result.** False. M(x) -> 1; in particular M(x) = O(1), so M(x) is not Omega(log log x).

**Argument.** sum_{n<=x} a(n) = sum_{P<=x} S(x-P), S(y) = number of semiprimes <= y, and
K(x) = number of primorials <= x.
1. Upper: sum <= K(x) S(x). Since p_i >= i+1, p_k# >= (k+1)!, so K(x) <= 1 + max{k : (k+1)! <= x}
   = (1+o(1)) log x / log log x (Stirling). Landau: S(x) = (1+o(1)) x log log x / log x (Hardy-Wright, Thm 437).
   Hence M(x) <= 1 + o(1).
2. Lower: for P <= x/log x, S(x-P) >= S(x(1 - 1/log x)) = (1+o(1)) S(x). The primorials p_k# <= x/log x include
   all k with theta(p_k) <= log x - log log x; by the prime number theorem (theta(y) ~ y, pi(y) ~ y/log y) there
   are (1+o(1)) log x / log log x of them. So M(x) >= 1 - o(1).
Only step 1 is needed to refute Theta(log log n). The likely source of the estimate: the trivial bound
K(x) <= log_2 x gives exactly log log x.

**Evidence.**
- Lean (Mathlib + `OpenProblemsLib.PNTApps`): [`A181674_mathlib.lean`](A181674_mathlib.lean), the refutation.
  `A181674_sum_le_mul` (sum_{n<=x} a(n) <= K(x) S(x)); `primorial_count_le` (K(x) <= M with M! <= x, from
  `factorial_le_primorial`: the primorial of the primes <= n is at least (pi(n)+1)!); the library's
  `semiprime_count_bound` (S(x) <= C x (1 + log(log_2 x + 1))/log x from Chebyshev and a dyadic Mertens
  bound) and `key_ineq` give `A181674_sum_le`: sum_{n<=x} a(n) <= C x for x >= 16; `A181674_not_loglog`:
  no c > 0 has c log log x <= (1/x) sum_{n<=x} a(n) for all large x. Checked 2026-11-08 with
  `tools/leancheck-mathlib.sh`: OK, axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: reproduces the 105 data terms; M(10^e) = 1.423, 1.510, 1.564, 1.570, 1.520 for
  e = 3..7 (K(x)S(x)/x = 1.50..1.71; log log x = 1.93..2.78). The convergence to 1 is too slow to see numerically.
- Outside Lean: the limit M(x) -> 1 (step 1 with Landau's asymptotic and step 2); the refutation of
  Theta(log log n) needs only M(x) = O(1), which is in Lean.

**Review level.** `lean-proof` (refutation in Lean; the limit 1 is a paper argument).

**Prior art.** Checked 2026-11-07: entry and history (#1-#11) keep the conjecture without comment; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs. No published discussion found; the refutation is
ours and elementary.
