# OEIS A135659: every Mersenne prime > 3 is ≡ 7 (mod 24)

**Source.** OEIS [A135659](https://oeis.org/A135659) (a(n) = 24n + 7). Conjecture: "All Mersenne
Primes (A000668) > 3 are in this sequence." (OEIS text, CC BY-SA 4.0.)

**Result.** True (elementary).

**Argument.** If 2^n - 1 > 3 is not divisible by 3, then n is odd (for even n, 3 | 4^(n/2) - 1)
and n ≥ 3. For odd n ≥ 3, 2^n ≡ 0 (mod 8) and 2^n ≡ 2 (mod 3), so 2^n ≡ 8 (mod 24) and
2^n - 1 ≡ 7 (mod 24). A Mersenne prime > 3 is not divisible by 3.

**Evidence.** [`A135659.lean`](A135659.lean): `mersenne_mod_24` for every n (core Lean,
induction on the exponent). Nothing outside Lean.

**Review level.** `lean-proof`.

**Prior art.** Verdict known, immediate (OEIS status resolved-in-entry; searched 2026-11-04). Folklore, stated as fact in A000668. Sources: [OEIS A135659 (fetched 2026-11-04)](https://oeis.org/A135659): conjecture text unchanged; [OEIS A000668 (fetched 2026-11-04)](https://oeis.org/A000668): states 'Mersenne primes other than the first are of the form 24n+7' (Jasinski 2007) with a mod-12 argument nearby. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A000668.
