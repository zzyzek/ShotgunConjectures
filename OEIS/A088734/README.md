# OEIS A088734: every two-digit prime is a term

**Source.** OEIS [A088734](https://oeis.org/A088734) ("First primes in p^p - 2m where p is
prime and m = 1,2.."), comment by Cino Hilliard: "Conjecture: 2,3,5,7,11,13,17,19 are the only
1 and 2 digit primes in the sequence." (OEIS text, CC BY-SA 4.0.)

**Reading.** The term for m is the first value x^x − 2m, with x running over the primes
2, 3, 5, 7, … in order, that is a positive prime. This is the entry's PARI program
(`forstep(m=2,n,2, forprime(x=2,n, y=x^x-m; if(isprime(y),...)))`, where PARI's
`isprime` is 0 on negative numbers); the program's bound n only truncates the output.
The listed data (2, 23, 3119, 19, 17, …) agree with this reading for 2m = 2, …, 38
(`certificate/chk.gp`).

**Result.** False. Every prime q with 10 ≤ q < 100 is a term, and 23 = a(2) is already in the
data.

**Argument.** Let q be prime, 10 ≤ q < 100, and 2m = 3125 − q ≥ 3026. Then 2^2 − 2m and
3^3 − 2m are negative and 5^5 − 2m = q is prime, so the term for this m is q. For example
2m = 3028 gives 97.

**Evidence.**
- Lean (core): [`A088734.lean`](A088734.lean). `A088734_97` (2m = 3028 gives 97) and
  `A088734_two_digit` (the statement above for all primes 10 ≤ q < 100), by `decide`; no axioms.
  Outside Lean: none.
- `certificate/chk.gp`: recomputes the data and the two-digit terms.

**Review level.** `lean-witness`.

**Prior art.** The entry still carries the comment (cached entry, revision 3, 2013; fetched
2026-11-07). google-deepmind/formal-conjectures (clone of 2026-11-06) and
otoi-lab/oeis-lean-proofs have no file for A088734.
