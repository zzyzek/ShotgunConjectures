# CFG C3: Mrs Perkins's quilt, f(n) beyond 100 and Selfridge's prime sets

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section C3. f(n) is the least number of squares in a prime (gcd 1) dissection of an n × n square
along lattice lines; values were known "with some slightly increasing lack of confidence" for
n ≤ 100. Selfridge noted (from the Brooks–Smith–Stone–Tutte finiteness theorem) that for each N all
but finitely many primes p have p × p squares that cannot be dissected into N squares, and the book
asks for this set of primes for each N.

**Reading.** For prime p and N ≥ 2, a dissection of p × p into N squares is automatically prime.
So the set asked for is {p prime : T(p, N) = 0}, where T(n, N) counts prime dissections of an n × n
square into N squares. Since T(n, N) > 0 forces f(n) ≤ N, only finitely many p need checking.

**Result.** Answered computationally elsewhere for the computable range.
- f(n) is now known exactly for n ≤ 120 (E. Wynn, b-file of OEIS A005670, 2013), with the n ≤ 100
  values confirmed.
- E. Wynn, *Exhaustive generation of Mrs Perkins's quilt square dissections for low orders*,
  Discrete Math. 334 (2014) 38–47, arXiv:1308.5420, generated all prime dissections of order
  N ≤ 18 (plantri on triangulations, cross-checked by a direct method). Its Table 1 gives T(n, N)
  for every n and N ≤ 18, and its Table 3 gives the largest size g(N) (OEIS A089047). This settles
  Selfridge's set for every N ≤ 18: the primes p ≤ g(N) with T(p, N) = 0, together with all primes
  p > g(N).
The question "for each N" (all N) is a request for an infinite table and has no closed answer.

**Evidence.** Citation only; no Lean (the exhaustive generation is a large computation). The
prime sets were not re-derived here.

**Review level.** `agent` (citation read: abstract, Table 1 caption and Section 4 text of
arXiv:1308.5420; table values not re-derived).

**Prior art.** OEIS A005670 (b-file to 120, Ed Pegg Jr. table of best known values up to 40000),
A089047, A221841; Wynn 2014. Checked 2026-11-07.
