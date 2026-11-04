# OEIS A188647: a(n) = k a(n-1) - (k-1)/k^n is an integer sequence

**Source.** OEIS [A188647](https://oeis.org/A188647), conjecture by C. Hohn: with k = ((x^2+y)^(1/2)+x)^2
and a(0) = 1, "for all integers x>=1 and y=[+-]1, k may be irrational, but sequence
a(n)=a(n-1)*k-((k-1)/(k^n)) always produces integer sequences"; this entry is y = 1 (A188646 is the
other sign). (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** By induction a(n) = (k^(n+1) + k^(-n))/(k+1): a(0) = 1, and
k (k^n + k^(1-n))/(k+1) - (k-1)k^(-n) = (k^(n+1) + k^(2-n) - k^(2-n) + k^(-n))/(k+1). Then
(k^(n+1) + k^(-n))/(k+1) = k^(-n) (k^(2n+1) + 1)/(k+1) = sum_{i=0}^{2n} (-1)^i k^(i-n)
= (-1)^n [1 + sum_{j=1}^{n} (-1)^j (k^j + k^(-j))], and k^j + k^(-j) = 2 T_j(2x² + y) is an
integer (OEIS-A188644/A188645, using 1/k = (√(x²+y) - x)² since y² = 1).

**Evidence.**
- `certificate/a188644.py`: exact arithmetic in Q(√(x²+y)) for x ≤ 8, n < 24, both signs: the
  recurrence values have zero √ part and integer rational part.
- Lean (Mathlib): [`A188647_mathlib.lean`](A188647_mathlib.lean), `A188647_main`: for every integer x >= 1, y = 1 or y = -1, and n, the real number a(n) defined by a(0) = 1, a(n) = a(n-1)k - (k-1)/k^n with k = (√(x²+y) + x)² is an integer (both signs, so A188646 too). Proof via a(n)(k+1) = k^(n+1) + k^(-n) and a(n) = w(n) - a(n-1) with the integer sequence w(n) = k^n + k^(-n). Outside Lean: none.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Prior art.** Known. [OEIS A188647](https://oeis.org/A188647) (fetched 2026-11-04) contains Manyama's Chebyshev form and an explicit integer binomial-sum formula (2019), which prove the conjecture; the 'Conjecture' label is stale. Searched: entry, OEIS cross-reference search, edit history. (Prior-art review 2026-11-04.)
