# OEIS A110076: 10^n is a value of sigma for every 4 ≤ n ≤ 500

**Source.** OEIS [A110076](https://oeis.org/A110076) (a(n) = largest m with σ(m) = 10^n, 0 if
none), comment: "Conjecture: For n>3 a(n) is positive." (OEIS text, CC BY-SA 4.0.)

**Result (partial; the conjecture stays open).** a(n) > 0 for every 4 ≤ n ≤ 500. Moreover the
conjecture implies that there are infinitely many primes of the form 2^a 5^b − 1, an open
problem of the same kind as the infinitude of Mersenne or Pierpont primes.

**Argument.**
1. Witnesses. For each n ≤ 500, `certificate/reps.out` lists distinct primes p_i = 2^{a_i}5^{b_i} − 1
   with Σ a_i = Σ b_i = n (two primes for 492 values of n, three for 5 values, e.g. n = 235, 262),
   so m = Π p_i has σ(m) = Π (p_i + 1) = 10^n. All 507 primes used are proved prime by Morrison's
   N + 1 test (N + 1 = 2^a 5^b is fully factored; `certificate/cert.gp`, one Lucas sequence with
   kronecker(D, N) = −1 per prime factor of N + 1).
2. Reduction. Let σ(p^e) have no prime factor other than 2, 5 (e ≥ 1). If e + 1 has an odd prime
   factor r, then s = (p^r − 1)/(p − 1) divides σ(p^e) and is odd (for p odd), hence a power of 5;
   5 | s forces p ≡ 1 (mod 5) and then v_5(s) = v_5(r) ≤ 1 by lifting the exponent, so s ≤ 5,
   impossible since s ≥ 1 + p + p² > 5. So e + 1 = 2^j, σ(p^e) = Π_{i<j}(1 + p^{2^i}); 1 + p^4 ≡ 2
   (mod 5 and mod 4) excludes j ≥ 3, so e ∈ {1, 3} and (p + 1) | σ(p^e), i.e. p + 1 = 2^a 5^b.
   p = 2 and p = 5 are excluded directly (2^{e+1} − 1 ≡ 3 mod 4; σ(5^e) ≡ 1 mod 5 and is odd or
   divisible by 3). Hence every m with σ(m) = 10^n is a product of primes 2^a 5^b − 1 to the first
   or third power; if there were finitely many such primes, σ(m) would be bounded.

**Evidence.** `certificate/qlist.gp` (all BPSW-probable primes 2^a5^b − 1, a, b ≤ 500: 1283),
`certificate/reps.py` → `reps.out`, `certificate/cert.gp` → `cert.out` ("certified 507
failures 0"). No Lean: the primality proofs are Lucas-sequence computations on numbers of up to
~700 digits (an N + 1 certificate checker is not in lib/OpenProblemsLib). Outside Lean: all.

**Review level.** `rechecked`.

**Prior art.** The entry has data to n = 23 and a comment (Wasserman, 2008) about n ≤ 103; no
proof of the conjecture and no reduction recorded (cached entry, 2026-11-07).
google-deepmind/formal-conjectures (clone of 2026-11-06) and otoi-lab/oeis-lean-proofs have no
file for A110076.
