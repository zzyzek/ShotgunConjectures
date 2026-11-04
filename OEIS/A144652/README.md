# OEIS A144652: if h is not a term, then 4h + 1 is prime (h ≥ 1)

**Source.** OEIS [A144652](https://oeis.org/A144652): triangle T(m,n) = floor((2mn+m+n)/2),
m ≥ n ≥ 1. Conjecture (Librandi, 2012): "If h does not belong to the sequence, then 4*h+1 is
prime." (OEIS text, CC BY-SA 4.0.)

**Reading.** h ranges over positive integers. For h = 0 (not a term) 4h + 1 = 1 is not prime.

**Result.** True for h ≥ 1.

**Argument.** Contrapositive. If 4h + 1 = d e with d, e > 1, then d = 2a+1, e = 2b+1 with
a, b ≥ 1 and 4ab + 2a + 2b + 1 = 4h + 1, so a + b is even and h = ab + (a+b)/2 = T(max, min).

**Evidence.**
- [`A144652.lean`](A144652.lean): `composite_is_term`, for all h, d, e (core Lean). Nothing
  outside Lean.
- `certificate/a140869.py` (covers both entries): for h ≤ 10^5 the only h not in the triangle with
  4h + 1 not prime is h = 0.

**Review level.** `lean-proof`.

**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). Sundaram-type argument; the specific statement is not written anywhere found. Sources: [OEIS A144652 (fetched 2026-11-04)](https://oeis.org/A144652): Librandi's conjecture unchanged; [Sieve of Sundaram (1934), standard factorisation argument](https://en.wikipedia.org/wiki/Sieve_of_Sundaram): same contrapositive: odd composites 2ab+a+b-type tables. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
