# OEIS A088104: an n-digit prime beginning with prime(n) always exists

**Source.** [A088104](https://oeis.org/A088104) (smallest n-digit prime beginning with prime(n), 0 if none),
comment: "Conjecture: No term is zero." (OEIS text, CC BY-SA 4.0.) The entry notes that Legendre's conjecture
would imply it (C. W. Wu, 2019).

**Result.** True (no term is zero), given Dusart's 2010 short-interval bound.

**Argument.** Let P = prime(n) have d digits (d ≤ n). The candidates are the integers in [x, x + 10^(n−d))
with x = P·10^(n−d) ≥ 10^(n−1), i.e. [x, x + x/P). Dusart (2010): for x ≥ 396738 there is a prime in
(x, x(1 + 1/(25 ln² x))]. For n ≥ 7, x ≥ 10^6 and 25 ln² x ≥ 25(n−1)² ln² 10 > 132(n−1)² > P (as
prime(n) < n(ln n + ln ln n) for n ≥ 6), so that prime lies in [x, x + x/P). For n ≤ 14 the terms are
found directly (n = 1: a(1) = 2).

**Evidence.**
- `certificate/check.py`: a(1..14) (deterministic Miller–Rabin) and P < 25 ln²(10^(n−1)) for 2 ≤ n ≤ 10^5.
- Lean: needs Mathlib and more (Dusart's explicit bound is not in Mathlib).

**Review level.** `rechecked`.
**Prior art.** New: [A088104](https://oeis.org/A088104) has it only conditionally on Legendre's conjecture (C. W. Wu, 2019); the unconditional proof from Dusart's short-interval bound is not stated anywhere found. Searched OEIS entry, references and history, web. Checked 2026-11-04.
