# Guy A3: more primes (16^p + 1)/17 beyond p = 317

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A3 (p. 16). McIntosh noted that the largest known prime of the form
(2^(4p) + 1)/17 had p = 317 and that it is composite for all primes 317 < p < 10000; Guy asks
whether there are any more.

**Result.** Yes, as probable primes. OEIS A057182 (numbers n with (16^n + 1)/17 prime) lists
n = 30197 (Robert G. Wilson v, 2005) and n = 1025393 (Paul Bourdelais, 2014, marked as a
probable prime). Both exponents are prime. This is a literature answer, not a resolution by
the scan.

**Argument.** None beyond the citation. No primality proof of either number was found; the
OEIS entry does not mention one, so the answer is at probable-prime level.

**Evidence.** OEIS A057182 read on 2026-11-01 (data 3, 5, 7, 23, 37, 89, 149, 173, 251, 307,
317, 30197, 1025393). Primality of the exponents 30197 and 1025393 checked with Miller–Rabin.
No Lean (a 36000-digit PRP is out of reach for core Lean).

**Review level.** `agent` (citation checked, nothing recomputed).
**Prior art.** OEIS A057182, Dubner & Granlund (J. Integer Seq. 2000) on (b^n+1)/(b+1).
