# OEIS A088987: the number of primes between consecutive prime-indexed primes is odd

**Source.** [A088987](https://oeis.org/A088987), comment: "Conjecture: There cannot be an even number total
of primes between two consecutive prime-indexed primes." (OEIS text, CC BY-SA 4.0.)

**Result.** True except for the first pair: between prime(2) = 3 and prime(3) = 5 there are 0 primes,
an even number. The entry already notes this exception.

**Argument.** Between prime(a) and prime(b) (a < b) lie exactly b − a − 1 primes. For consecutive primes
a = p_x, b = p_{x+1} with x ≥ 2 both are odd, so b − a − 1 is odd. For x = 1, b − a − 1 = 0.

**Evidence.** `certificate/check.py` (all pairs below 10^6). No Lean file.

**Review level.** `rechecked`.
**Prior art.** The exception is stated in the entry (checked 2026-11-01). Resolved by others.
