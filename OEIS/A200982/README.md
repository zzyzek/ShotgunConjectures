# OEIS A200982: the terms have asymptotic density zero (known)

**Source.** [A200982](https://oeis.org/A200982): k with 1^(lambda(k)/2) + ... + (k-1)^(lambda(k)/2) = 0 (mod k),
lambda = Carmichael's function. Conjecture in the entry: "The asymptotic density is zero." (Entry fetched via the
scan cache, 2026-11-07.)

**Reading.** For k = 2, lambda(2)/2 = 1/2 is not an integer and 2 is not a term; k = 1 is a term (empty sum).

**Result.** True, and known: J. M. Grau and A. M. Oller-Marcén, *About the congruence sum_{k=1}^n k^{f(n)} = 0
(mod n)*, arXiv:1304.2678 (2013), Proposition 12 (characterisation) and Proposition 13 (zero density) for
f = lambda/2.

**Argument (re-derived here).** Let L = lambda(k)/2, t = v2(lambda(k)), and S = sum_{j<k} j^L. By CRT, k | S iff
p^e | S for each p^e || k, and S = (k/p^e) * sum_{j mod p^e} j^L (mod p^e).

1. *Odd p.* p^(e-1) divides L and L >= e. If (p-1) does not divide L, the unit sum is a geometric sum with ratio
   g^L != 1 (mod p), hence 0, and non-units contribute p^L * (...) = 0: fine. If (p-1) | L then phi(p^e) | L, every
   unit contributes 1, and S = (k/p^e) phi(p^e), of p-adic valuation exactly e-1: k is not a term. So k is a term
   only if v2(p-1) = t for every odd p | k.
2. *p = 2.* S_e(L) = sum_{j<2^e} j^L. For L even, S_{e+1} = 2 S_e (mod 2^(e+1)) by the binomial expansion of
   (j+2^e)^L, so S_e = 2^(e-1) (mod 2^e): fails. For L odd, pairing j with 2^e - j leaves (2^(e-1))^L, which is
   0 mod 2^e iff (e-1)L >= e. L odd means t = 1, so every odd p is 3 mod 4 and e <= 3; e = 1 fails; e in {2, 3}
   needs L >= 3, i.e. k not in {4, 8, 12, 24}.
   Characterisation: k > 2 is a term iff either k is odd and all its prime factors p share v2(p-1), or k = 4m or
   8m with m > 3 odd and every prime factor of m equal to 3 mod 4. This is the paper's Proposition 12.
3. *Density.* Every term is 1, or has no prime factor = 3 mod 4, or has no prime factor = 1 mod 4. By Dirichlet,
   sum 1/p diverges over each class, and the integers avoiding a set of primes with divergent reciprocal sum have
   density zero (sieve: the density is at most prod (1 - 1/p) over any finite subset). Hence density zero.

Remark (not proved here). The dominant part is the set with all odd prime factors = 3 mod 4, which by the
Landau-Selberg-Delange method has about C x / sqrt(log x) elements up to x; the parts with v2(p-1) = s >= 2 have
x/(log x)^(1 - 2^-s) elements. So the count of terms up to x is of order x / sqrt(log x).

**Evidence.**
- [`certificate/check_A200982.py`](certificate/check_A200982.py): direct evaluation of the sum for k <= 6000
  agrees with the characterisation of step 2 (no mismatch), and the first terms agree with the entry.
- Lean: none. The local characterisation is elementary; the density step needs Dirichlet's divergence of
  sum 1/p over p = 3 mod 4 and p = 1 mod 4 (Mathlib has the divergence of sum log(p)/p over a class,
  `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`, not of sum 1/p) and a sieve density bound.
- Outside Lean: everything (steps 1-3); the cited paper proves the same statements.

**Review level.** `rechecked` (argument re-derived independently, characterisation checked numerically).

**Prior art.** Grau, Oller-Marcén, arXiv:1304.2678 (2013), Prop. 12-13, found 2026-11-07 by web search. Also
searched: OEIS entry (conjecture still present, paper not linked), google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs (no A200982).
