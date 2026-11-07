# OEIS A083184: no entry is zero for n <= 400 (partial; conjecture open)

**Source.** [A083184](https://oeis.org/A083184) (Amarnath Murthy and Meenakshi Srikanth, Apr 26 2003): "Smallest palindromic prime having a sum of digits = prime(n), or 0 if no such number exists." "Conjecture:
no entry is zero." (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Result.** Partial: a(n) != 0 for every n <= 400 (prime(n) <= 2741). For n <= 100 by proved primes; for
100 < n <= 400 by BPSW probable primes. The b-file (Chai Wah Wu) gives the least terms for n <= 35. The conjecture in
general implies that there are infinitely many palindromic primes, which is open.

**Method.** A witness is a palindrome of odd length 2k+1 (even-length palindromes are multiples of 11) with
middle digit c and half digit sum (p - c)/2; witness.gp samples random halves with that digit sum, filters with
BPSW (ispseudoprime) and, for n <= 100, proves primality with PARI's isprime (APR-CL). The witnesses are not
necessarily the least terms.

**Evidence.**
- [`certificate/witnesses_A083184.txt`](certificate/witnesses_A083184.txt): n, prime(n), length, "proved"/"bpsw", witness,
  for 5 <= n <= 400 (n <= 4: the one-digit primes 2, 3, 5, 7).
- [`certificate/witness.gp`](certificate/witness.gp), run scripts `run_A083184.gp` (first pass) and `run2_A083184.gp` (retries
  and n up to 400); PARI 2.x, `gp -q -D recover=0`, no errors (only the stack-size warning).
- [`certificate/verify.py`](certificate/verify.py): independent check of every line (palindrome, digits in
  {0123456789}, digit sum = prime(n), strong probable prime to 8 bases).
- Outside Lean: all of it (no Lean: primality certificates for 100- to 1000-digit numbers are out of reach of the
  repo's Pratt tooling). Probable primes for 100 < n <= 400 are not proved prime.

**Review level.** `rechecked` (two independent programs).

**Prior art.** Checked 2026-11-07: entry and b-file reference; infinitude of palindromic primes is open (best known:
infinitely many palindromes with at most 6 prime factors, Tuxanidy-Panario, arXiv:2307.16637). Obstruction analysis:
`open-problems/work/OEIS-A083184/REPORT.md`.
