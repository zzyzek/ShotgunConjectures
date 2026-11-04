# Guy B31: the gcd of two binomial coefficients can have all prime factors ≤ r (already in the book)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B31. Erdős and Szekeres ask whether the greatest prime factor of
gcd(C(n,r), C(n,s)), 0 < r < s ≤ n/2, always exceeds r. The book quotes the only
counterexample with r > 3 that they noticed, n = 28, r = 5, s = 14.

**Result.** No; the book already contains the counterexample, so this is a check, not a new
resolution. gcd(C(28,5), C(28,14)) = gcd(98280, 40116600) = 1080 = 2³·3³·5, greatest prime
factor 5 = r. With r ≤ 3 the counterexamples with n ≤ 60 are (n, r, s) = (10, 3, 5),
(16, 2, 6), (28, 3, 14).

**Argument.** Direct computation.

**Evidence.** Lean: [`B31_5.lean`](B31_5.lean) computes the binomial coefficients (from a
factorial), the gcd's and 1080 = 2³·3³·5 (no axioms). This proves the counterexample in full.
`certificate/misc_check.py` lists all counterexamples with n ≤ 60.

**Review level.** `lean-proof` (the statement "some prime factor bound fails" for these
numbers). **Note:** answered in the source; not a new result.
**Prior art.** Erdős & Szekeres (1978), as cited in the book. 2026-11-01.
