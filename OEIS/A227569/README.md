# OEIS A227569: F[a; b] = 2 reduced to six explicit digit processes (partial)

**Source.** [A227569](https://oeis.org/A227569): for complementary sets a, b of positive integers,
F[a; b] = F(a) + F(b) with F(x) = 1/x(1) + 1/(x(1)x(2)) + ... (Engel sums). Conjecture in the entry: no pair has
F[a; b] = 2. The entry also gives e - 1 ≤ F[a; b] ≤ 2.0594... (OEIS text, CC BY-SA 4.0, cached entry, checked
2026-11-07.)

**Result (partial; the conjecture stays open).** Every complementary pair with F[a; b] = 2 extends one of 6
explicit prefixes of length 600 (12 counting the swap of a and b). In each, one side is sparse (up to 300 it is
{4,6,15,23,29,61}, {1,2,3,5,22,51,104}, {4,5,49,106,154,195}, {1,2,3,7}, {3,29,36,42,183} or {1,2,8,67,91,264}),
and the pair exists iff the sparse side's strict Engel continuation never falls into a gap. Numerically
(3000-digit floating point, not interval arithmetic) all six continue past sparse-side elements of order 10^9 to
10^12. Heuristically each survives with probability about 0.997, so the conjecture is expected to be false, but
neither direction is proved.

**Argument.** F is monotone under inclusion and F(x) ≤ F({m, m+1, ...}) ≤ 1/(m-1) for x inside {m, m+1, ...}. After
deciding 1..n (1 in a by symmetry), with products Pa, Pb and partial sums Sa, Sb, every completion lies in
[Sa + Sb + min(1/Pa, 1/Pb)/(n+1), Sa + Sb + (1/Pa + 1/Pb)/n]. Discarding prefixes whose interval misses 2, in exact
rational arithmetic, leaves 12 prefixes at every checked depth from 10 to 600 (multiples of 5). Beyond them the
dense side contributes less than 1/n! and the sparse side must realise a fixed residual x as a strictly increasing
Engel sum: digit y = ⌈1/x⌉ is allowed iff x ≤ (1 + F({y+1, ...}))/y, then x ← yx - 1.

**Evidence.**
- [`certificate/bbq.py`](certificate/bbq.py) (exact, `fractions.Fraction`), output [`certificate/bb600.out`](certificate/bb600.out).
- [`certificate/tail.py`](certificate/tail.py) (mpmath, 3000 digits), output [`certificate/tail300.out`](certificate/tail300.out).
- Lean: none. Outside Lean: the bounds (paper) and both computations.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07: OEIS entry, formal-conjectures, oeis-lean-proofs: nothing found. Obstruction
analysis in the scan repo, work/OEIS-A227569/REPORT.md.
