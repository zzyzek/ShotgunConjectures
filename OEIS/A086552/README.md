# OEIS A086552: tau(x)/tau(x-1) = n is solvable for every n (known); the least solution need not have x-1 prime

**Source.** [A086552](https://oeis.org/A086552): numbers x such that tau(x)/tau(x-1) is an integer. "Conjecture:
(1) tau(x)/tau(x-1) = n has solutions for every n. (2) If x is the smallest number for a given n such that
tau(x)/tau(x-1) = n > 1, then x-1 is a prime." (OEIS text, CC BY-SA 4.0, cached entry read 2026-11-07.)

**Result.**
- (1) True: S. Eberhard, "Ratios of consecutive values of the divisor function", J. Number Theory 281 (2026),
  arXiv:2505.00727, proves that d(n+1)/d(n) takes every positive rational value infinitely often.
- (2) False. For n = 17 the least x is 983040 = 2^16 * 3 * 5, with tau(x) = 68, and x-1 = 983039 = 241 * 4079,
  tau(x-1) = 4. Further counterexamples below 4*10^8: n = 23 (x = 62914560 = 2^22*3*5, x-1 = 3361*18719) and
  n = 34 (x = 6881280 = 2^16*3*5*7, x-1 = 109*63131). For all other n < 2000 with a solution x <= 4*10^8, the
  least x has x-1 prime.

**Argument for n = 17.** If 17 | tau(x), some p^a || x has 17 | a+1, so a >= 16. For x < 983040 = 2^16*15 this
forces p = 2 (3^16 > 983040) and x = 2^16 m with m odd, m <= 13. The seven values m = 1, 3, ..., 13 give
tau(x)/tau(x-1) = 17/16, 34/4, 34/4, 34/8, 51/8, 34/16, 34/12, never 17 (check.py lists the factorizations).
So 983040 is the least solution, and 983039 = 241 * 4079.

**Evidence.** [`certificate/check.py`](certificate/check.py) (the n = 17 argument, with factorizations);
[`certificate/sieve.c`](certificate/sieve.c) with output [`certificate/out.txt`](certificate/out.txt): exhaustive
divisor-count sieve to 4*10^8, least x for each n < 2000. Lean: none. Outside Lean: the seven-case check (sympy)
and Eberhard's theorem for (1).

**Review level.** `rechecked` (minimality for n = 17 by the 2^16 argument and independently by the sieve).

**Prior art.** Checked 2026-11-07. Part (1): Eberhard (arXiv:2505.00727, JNT 2026), found by web search; the
entry does not cite it. Part (2): no counterexample in the entry or found by search. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
