# OEIS A110034: |row sums| of the Fibonacci–Hankel characteristic polynomials are partial sums of A061646

**Source.** OEIS [A110034](https://oeis.org/A110034) (row sums of A110033, offset 0), comment by J. M. Bergot
(Jun 10 2013): "Conjecture: |a(n)| = Sum_{k=1..n-1} A061646(k)."

**Reading.** A110033 row n: coefficients of the characteristic polynomial det(xI − H_n) of the n×n Hankel matrix
H_n = (F(i+j−1))_{1≤i,j≤n} (row 0 = 1). The row sum is the polynomial at x = 1, det(I − H_n).
A061646 has offset −1: a(−1) = a(0) = a(1) = 1, a(n) = 2a(n−1) + 2a(n−2) − a(n−3).

**Result.** True for every n ≥ 1, with a(n) = −Σ_{k=1..n−1} A061646(k) ≤ 0. False as stated at n = 0:
a(0) = 1 and the sum is empty (0). Corrected statement: n ≥ 1.

**Argument.** F(i+j+1) = F(i)F(j) + F(i+1)F(j+1), so H_n = U Uᵀ with U the n×2 matrix of rows (F(i+1), F(i)),
i = 0..n−1. Weinstein–Aronszajn: det(I − U Uᵀ) = det(I₂ − Uᵀ U)
= (1 − Σ F(i+1)²)(1 − Σ F(i)²) − (Σ F(i)F(i+1))². The sums are F(n)F(n+1), F(n−1)F(n) and F(n)² − [n odd];
A061646(k) = 2F(k)² + (−1)^k; the identity reduces to Cassini's F(m+1)² − F(m)F(m+1) − F(m)² = (−1)^m.

**Evidence.**
- Lean (Mathlib): [`A110034_mathlib.lean`](A110034_mathlib.lean). `A110034_conjecture (n : ℕ) (hn : 1 ≤ n) :
  |A110034 n| = Σ_{k ∈ Ico 1 n} A061646 k`, `A110034_formula` (a(n) = −Σ), `A110034_zero` (a(0) = 1, sum 0),
  with A110034 defined from `Matrix.charpoly`. Supporting: `A110034_det`, `A110034_H_eq`, `A110034_det2`,
  `A110034_cassini`, `A061646_closed`, `A110034_data`. Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: exact characteristic polynomials (sympy) for n ≤ 25 against the entry and the sum.
- Outside Lean: nothing beyond the reading above.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: OEIS A110034, A110033, A061646 entries (the entry prints a g.f. and
a(n) = Σ_{k<n} F(k)F(k+1) − F(2n) + 1 without proof), web search, google-deepmind/formal-conjectures (no file).
The rank-2 structure of Fibonacci Hankel matrices is classical (cf. OEIS A114534, Weston 1998). No proof of the
conjecture found.
