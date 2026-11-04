# OEIS A113599: no term is zero (pigeonhole)

**Source.** [A113599](https://oeis.org/A113599) (least n-digit multiple of n whose digit permutations give at least
n distinct multiples of n, 0 if none), comment: "Conjecture: No term is zero. The proof should be simple."
(OEIS text, CC BY-SA 4.0.)

**Result.** True. Proved in the entry by J. Rayman (Feb 2023); re-derived here.

**Argument.** There are at least ⌊9·10^(n−1)/n⌋ n-digit multiples of n and C(n+9, 9) multisets of n digits, so
some multiset carries at least ⌈⌊9·10^(n−1)/n⌋/C(n+9, 9)⌉ of them; these are distinct n-digit multiples of n that
are digit permutations of one another. The bound is ≥ n for every n ≥ 4 (it grows by a factor ≈ 10n/(n+10) per
step); n = 1, 2, 3 have the terms 1, 20, 102.

**Evidence.** `certificate/check.py`: the bound ≥ n for 4 ≤ n ≤ 2000 (exact integers). No Lean file.

**Review level.** `rechecked`.
**Prior art.** J. Rayman, comment in A113599 (checked 2026-11-01). Resolved by others.
