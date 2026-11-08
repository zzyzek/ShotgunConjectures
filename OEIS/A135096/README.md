# OEIS A135096: n = floor(m^c) + p fails for some c in [L, U]

**Source.** OEIS [A135096](https://oeis.org/A135096) (decimal expansion of a constant L) and
[A135097](https://oeis.org/A135097) (a constant U), comment by Werner D. Sand (2007):
"Conjecture: With any real number c in the interval [L,U] there exists for each natural number
n>2 a natural number m and a prime number p so that n=floor(m^c)+p. L is the lower bound of c.
U is the upper bound of c. L = 0.5781296526305628137240577579803... U =
1.3652123889685187297293386676777... (A135097)." (OEIS text, CC BY-SA 4.0.)

**Reading.** m ranges over m ≥ 0 (allowing m = 0 makes every prime n representable and so
only weakens a counterexample); with m ≥ 1 the failures below are a subset of the failures.

**Result.** False. For c = 1.31 the number n = 16 is not floor(m^c) + p: the values
floor(m^1.31), m = 0, …, 8, are 0, 1, 2, 4, 6, 8, 10, 12, 15 and 16 minus each of them
(16, 15, 14, 12, 10, 8, 6, 4, 1) is never prime; for m ≥ 9, m^1.31 ≥ 17.8.

The exact set of c in [1, 1.4] for which some n ≤ 60 fails (endpoints are log v / log m,
computed with 40-digit arithmetic at every breakpoint, `certificate/exact.py`):

| c interval | failing n |
|---|---|
| [log 26/log 14, log 24/log 13) = [1.2345683…, 1.2390318…) | 27 |
| [log 20/log 10, log 15/log 8) = [1.3010300…, 1.3022969…) | 26 |
| [log 15/log 8, log 13/log 7) = [1.3022969…, 1.3181232…) | 16 |
| [4/3, log 11/log 6) = [1.3333333…, 1.3382908…) | 22 |
| [log 9/log 5, …) = [1.3652123889719…, …) | 10 |

A grid scan with 37 001 values of c in [1, 1.37] and all n ≤ 3000 (`certificate/scan.c`)
finds no other failures, and nine sample values of c outside these intervals have no failure
for n ≤ 2·10^6.

Two further corrections:
- L is not a lower bound. For every c in (0, 1] the values floor(m^c), m ≥ 1, take every
  positive integer (consecutive powers differ by at most 1), so n = (n − 2) + 2 for all n ≥ 3.
- The true upper end of the last good interval is log 9/log 5 = 1.36521238897197…; the
  constant in A135097 (1.3652123889685…) agrees only to 11 digits. At c = log 9/log 5 itself
  n = 10 fails (5^c = 9), so U as defined there is not attained.

Under the reading m ≥ 1 there are more failures (prime n such as 29 and 23), and the entry's
example c = 1.23456789 fails at n = 29; with m ≥ 0 the example is correct (it lies just below
log 26/log 14).

**Argument.** For c = 131/100, v = floor(m^c) is the integer with v^100 ≤ m^131 < (v + 1)^100.
For m ≥ 9, m^131 ≥ 9^131 > 15^100, so v ≥ 15 and v + p ≥ 17. For m ≤ 8 the values are listed
above.

**Evidence.**
- Lean (core): [`A135096.lean`](A135096.lean). `A135096_c131_n16`: for all m, v, p with
  v^100 ≤ m^131 < (v + 1)^100 and p prime, v + p ≠ 16. Axioms propext, Quot.sound; zero
  warnings. Outside Lean: none for the disproof; the interval table and the corrections on L
  and U are computations and short arguments given here only.
- `certificate/exact.py` (breakpoint table), `certificate/scan.c` (grid scan).

**Review level.** `lean-witness`.

**Prior art.** No correction in A135096 or A135097 (cached entry and fetched A135097,
2026-11-07). google-deepmind/formal-conjectures (clone of 2026-11-06) and
otoi-lab/oeis-lean-proofs have no file for A135096 or A135097. The asymptotic question (every
large n is floor(m^c) + p for c slightly above 1) is a Piatetski-Shapiro–Goldbach type problem
and is not addressed here.
