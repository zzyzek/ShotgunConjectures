# OEIS A140869: if h is not a term, then 4h + 5 is prime

**Source.** OEIS [A140869](https://oeis.org/A140869): triangle T(m,n) = floor((2mn+m+n-2)/2),
m ≥ n ≥ 1. Conjecture (Librandi, 2012): "If h does not belong to the sequence, then 4*h+5 is
prime." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Contrapositive. If 4h + 5 = d e with d, e > 1, both are odd, d = 2a+1, e = 2b+1 with
a, b ≥ 1, and 4ab + 2a + 2b + 1 = 4h + 5. So a + b is even and h = ab + (a+b)/2 - 1 =
floor((2ab + a + b - 2)/2) = T(max, min).

**Evidence.**
- [`A140869.lean`](A140869.lean): `composite_is_term`, for all h, d, e (core Lean). Nothing
  outside Lean.
- `certificate/a140869.py`: h ≤ 10^5 not in the triangle all give 4h + 5 prime.

**Review level.** `lean-proof`.

**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). Sundaram-type argument; the specific statement is not written anywhere found. Sources: [OEIS A140869 (fetched 2026-11-04)](https://oeis.org/A140869): Librandi's conjecture unchanged; [OEIS A153085 (fetched 2026-11-04)](https://oeis.org/A153085): numbers k with 4k+5 not prime; does not state the equivalence; [Sieve of Sundaram (1934), standard factorisation argument](https://en.wikipedia.org/wiki/Sieve_of_Sundaram): same contrapositive: odd composites 2ab+a+b-type tables. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A153085.
