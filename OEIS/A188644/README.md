# OEIS A188644: (k^n + k^(-n))/2 is an integer for k = (√(x²-1) + x)²

**Source.** OEIS [A188644](https://oeis.org/A188644), conjecture by C. Hohn: "Given function
f(x, y)=((x^2+y)^(1/2)+x)^2; and constant k=f(x, y); then for all integers x>=1 and y=[+-]1,
k may be irrational, but ((k^n)+(k^(-n)))/2 always produces integer sequences"; this entry is
the case y = -1 (A188645 is the other sign). (OEIS text, CC BY-SA 4.0.)

**Result.** True: (k^n + k^(-n))/2 = T_n(2x^2 + y), with T_n the Chebyshev polynomial of the
first kind.

**Argument.** Since y^2 = 1, 1/k = (√(x²+y) - x)² / y² = (√(x²+y) - x)², so
k + 1/k = 2(2x² + y). Put m = 2x² + y; u_n = (k^n + k^(-n))/2 satisfies u_0 = 1, u_1 = m,
u_(n+1) = 2m u_n - u_(n-1), which is the Chebyshev recurrence: u_n = T_n(m) ∈ Z.
(Equivalently, the entry's comment A(n,k) = T_(2k)(n) by Manyama.)

**Evidence.**
- `certificate/a188644.py`: exact arithmetic in Z[√(x²+y)] for x ≤ 8, n < 24, both signs:
  k^n + k^(-n) has zero √ part and equals 2 T_n(2x²+y).
- Lean (Mathlib): [`A188644_mathlib.lean`](A188644_mathlib.lean), theorem `A188644_conjecture`: for x ≥ 1 and all n,
  with k = (√(x² − 1) + x)² in ℝ, (k^n + k^(−n))/2 = T_n(2x² − 1) with T_n = `Polynomial.Chebyshev.T ℤ n`
  (`A188644_integer`: it is an integer). The core lemma covers both signs. Nothing outside Lean.

**Review level.** `lean-proof`.

**Prior art.** Known. [OEIS A188644](https://oeis.org/A188644) (fetched 2026-11-04) contains Manyama's Chebyshev identity and an explicit binomial-sum formula (2018-2019), which prove integrality; the 'Conjecture' label is stale. Searched: entry, OEIS cross-reference search, edit history. At most a request to drop the label. (Prior-art review 2026-11-04.)
