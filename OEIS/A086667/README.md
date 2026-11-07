# OEIS A086667: T(n,k) -> 10^k - 1 holds for k <= 14 (partial, from the literature; open in general)

**Source.** [A086667](https://oeis.org/A086667) (Reinhard Zumkeller, Jul 27 2003): T(n,k) = greatest decimal number of
length k occurring as a string among the first n digits of pi. "Conjecture: T(n,k) -> 10^k - 1." (OEIS text, CC
BY-SA 4.0, checked 2026-11-07.)

**Reading.** For fixed k, T(n,k) is nondecreasing in n and bounded by 10^k - 1, so it is eventually constant, equal to
the largest k-digit block anywhere in pi. Hence T(n,k) -> 10^k - 1 iff k consecutive 9s occur in pi, and the
conjecture for all k says pi has arbitrarily long runs of 9s.

**Result.** Partial: true for every k <= 14, since runs of k nines occur in pi for k <= 14 (first occurrences
tabulated in [A048940](https://oeis.org/A048940): position 762 for k = 3..6, ..., 5758910552709 for k = 13, 14;
S. Kondo 2011; A048940 notes a(15) > 2.2e13). Open for k >= 15. Implied by the normality of pi (open).

**Evidence.** Citation only (A048940 and its b-file, read 2026-11-07); nothing recomputed. lean_status none.
Outside Lean: all of it.

**Review level.** `agent`.

**Prior art.** A048940 (Weisstein, Resta 2019, Kanada laboratory 2002, Kondo 2011, Petukhov 2020).
