# OEIS A049048: partial result on n! = 1 (mod c) for composite c

**Source.** [A049048](https://oeis.org/A049048): composite numbers n such that k! = 1 (mod n) for some k > 2.
Conjecture in the entry: if c is composite then n! = 1 (mod c) for at most one n >= 2. (OEIS text, CC BY-SA 4.0,
checked 2026-11-01 by the scan.)

**Result (partial; the conjecture stays open).**
1. Reduction: the conjecture is equivalent to "gcd(n! - 1, m! - 1) is 1 or a prime for all 2 <= n < m", and to
   "no prime square p^2 and no product pq of distinct primes is a counterexample".
2. No counterexample has its larger n at most 1200 (any c), and none has two prime factors (counted with
   multiplicity) at most 10^6.

**Argument for 1.** If n! = 1 (mod c), no prime <= n divides c. So in a counterexample (n < m) every prime factor
of c exceeds m, c divides g = gcd(n! - 1, m! - 1), and every composite divisor of c is again a counterexample.
Hence a counterexample exists iff some g is composite, iff some pq or p^2 is a counterexample.

**Evidence.**
- [`certificate/gcd.gp`](certificate/gcd.gp): all 2 <= n < m <= 1200; 520 pairs with g > 1, all g pass
  `ispseudoprime` (gp -q -D recover=0, exit 0, no errors).
- [`certificate/sp.c`](certificate/sp.c), [`certificate/pairs.py`](certificate/pairs.py): for every prime
  p <= 10^6, the set S_p = {n < p : n! = 1 mod p} (and mod p^2); no two primes share two elements, no p^2 has two.
- Lean: none. Outside Lean: the reduction (above) and both computations; the gcds are BPSW probable primes.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07: OEIS entry, formal-conjectures, oeis-lean-proofs: nothing found. Obstruction
analysis in the scan repo, work/OEIS-A049048/REPORT.md.
