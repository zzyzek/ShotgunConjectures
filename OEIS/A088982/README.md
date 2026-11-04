# OEIS A088982: a prime between consecutive prime-indexed primes

**Source.** [A088982](https://oeis.org/A088982), comment: "Conjecture: For x > 1 there is at least 1 prime
between prime(prime(x)) and prime(prime(x+1))." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial. The entry already contains the proof (M. F. Hasler, 2015).

**Argument.** For x > 1, prime(x) and prime(x+1) are odd, so prime(x+1) ≥ prime(x) + 2 and
prime(prime(x)) < prime(prime(x) + 1) < prime(prime(x+1)).

**Evidence.** `certificate/check.py` (all pairs below 10^6). No Lean file.

**Review level.** `rechecked`.
**Prior art.** Hasler's comment in A088982 (checked 2026-11-01). Resolved by others.
