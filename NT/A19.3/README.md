# Guy A19 (Cohen–Selfridge): the least odd number not of the form ±p^a ± 2^b

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A19.
Cohen and Selfridge ask for the least positive odd number not of the form ±p^a ± 2^b (p prime,
any signs). They note it exceeds 2^18 and give a 94-digit upper bound; Guy also cites Sun
Zhi-Wei's residue class modulo 66483084961588510124010691590 whose members are not ±p^a ± q^b,
which contains Cohen–Selfridge's 26-digit number 47867742232066880047611079. References:
F. Cohen, J. L. Selfridge, *Math. Comp.* 29 (1975) 79–81; Z.-W. Sun, *Proc. AMS* 128 (2000)
997–1002.

**Reading.** We use the most demanding reading for the non-representation claims: p any
prime (p = 2 allowed), a ≥ 0, b ≥ 0. For the representation search we use the least generous
one: a ≥ 1, b ≥ 1 (then p is odd, since n is odd). So both bounds hold under every reading.

**Result (partial; the exact value stays open).**

1. *New upper bound.* x₀ = 10439679896374780276373 (23 digits, ≈ 1.04·10²²) is odd and is not of the form
   ±p^a ± 2^b. So the least such number is at most x₀, improving the 26-digit bound
   47867742232066880047611079 ≈ 4.79·10²⁵ (Cohen–Selfridge / Sun) by a factor of about 4600. Residues: x₀ ≡ 1 (mod 2) and x₀ mod (3, 5, 7, 11, 13, 17, 19, 31, 37,
   41, 61, 73, 97, 109, 151, 241, 257, 331) = (2, 3, 1, 5, 5, 9, 5, 2, 16, 10, 49, 2, 31, 93, 32, 120,
   129, 4).
2. *New lower bound.* Every odd n < 42565109 is p^a + 2^b, p^a − 2^b or 2^b − p^a with p
   prime, a ≥ 1, b ≥ 1, every prime proved (previous published bound 2^18 = 262144). Up to
   2^28 = 268435456 the same holds except for three n: 42565109 and 52274777, whose only
   representations found use probable primes (2^5945 + n, 1790 digits; 2^16116 − n, 4852
   digits), and 111827383 = 239 · 467897, for which no representation exists with b ≤ 26000
   (primes, PRP test) or with b ≤ 5000 (prime powers). These three have no representation with
   b ≤ 5000; between 92% and 97%
   of the numbers n ± 2^b (b ≤ 2000) have a prime factor below 1000, so they behave like
   Sierpiński-type candidates with an almost-covering. p^a with a ≥ 2 was needed for 24 n.
3. *Why covering numbers sit near 10²²–10²⁵ (structure).* Among two-sided coverings with
   moduli dividing 720 built from primes below 10⁷ (x ≡ 2^c mod p covers b ≡ c for x − 2^b and,
   when ord_p(2) is even, b ≡ c + ord/2 for x + 2^b), the least possible product of the
   primes is between 10^28.519 (HiGHS dual bound) and 10^28.522, the latter attained by the 18 primes 3, 5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 97,
   109, 151, 241, 257, 331 (ILP, HiGHS, L = 720); these are exactly the
   primes behind the Cohen–Selfridge/Sun number. A covering x is the least positive member of a
   class modulo 2·∏p ≈ 6.65·10²⁸, and each covering gives 1440 classes (x → ±2^t x).

**Argument for item 1.** With S the 18 primes above and L = 720:
- *Covering.* For every b mod 720, some p ∈ S divides x₀ − 2^b and some p ∈ S divides
  x₀ + 2^b (ord_p(2) | 720 for all p ∈ S, so this is a finite check).
- *Two primes.* If two distinct primes of S divide |x₀ ∓ 2^b|, it is not a prime power.
- *One prime p (single classes).* Then |x₀ ∓ 2^b| = r^a forces r = p. For b ≥ 20 in the class
  b ≡ b₀ (mod 720), the equation ε p^a = x₀ − 2^b (ε = ±1) or p^a = x₀ + 2^b implies
  ε p^a ≡ x₀ (mod 2^20) and ε p^a ≡ x₀ ∓ 2^{b₀} (mod q) for every prime q with ord_q(2) | 720.
  These restrict a modulo ord_{2^20}(p) and modulo ord_q(p); for every single class the
  combined set of admissible a is empty.
- *Small b.* For b < (bit length of x₀) + 721 the numbers |x₀ ∓ 2^b| are computed exactly: each
  is > 1, has a prime factor in S, and is not a power of that prime.
- The four shapes x₀ = p^a + 2^b, p^a − 2^b, 2^b − p^a (and −p^a − 2^b < 0) are exactly the
  cases x₀ − 2^b = ±p^a and x₀ + 2^b = p^a, so x₀ has no representation.
x₀ was found by sampling coverings on S with CaDiCaL (random relabellings), taking for each
covering the least odd CRT solution over its orbit x → ±2^t x.

**Evidence.** `certificate/verify_x.py` (sympy) and `certificate/verify_x.gp` (PARI, written
separately) both print PROVED / 1 for x₀ and for 47867742232066880047611079 (control).
`certificate/satcov.py` (search), `certificate/ilp.py` (minimum product, item 3),
`certificate/cs.c` (item 2; deterministic Miller–Rabin with Sinclair's 7 bases, exact for
n < 2^64, b ≤ 62), `certificate/hard.gp` (the 43744 odd n < 2^28 with no representation
with b ≤ 62; all but three resolved with b ≤ 4357 and PARI `isprime`, a primality proof),
`certificate/ext.gp` (PRP search b ≤ 40000 for the three), logs `cs_2e28.txt`,
`hard_out.txt`, `ext_*.txt`, `verify_best_py.txt`, `verify_best_gp.txt`.
No Lean. A Lean proof of item 1 is possible in principle (covering tables, periodicity of
2^b and p^a modulo q, 1482 exclusion tables, about 1500 big-number checks) but was not written.
Outside Lean: everything.

**Review level.** rechecked (two independent verifier implementations for item 1).

**Prior art (2026-11-07).** Cohen–Selfridge 1975 (lower bound 2^18, 94-digit upper bound and a
26-digit number not ±p ± 2^b); Sun 2000 (the class of that 26-digit number avoids ±p^a ± q^b).
Web searches found no smaller explicit example and no lower bound beyond 2^18. Guy's 2004 text
still quotes these bounds. google-deepmind/formal-conjectures: no entry for this question.
