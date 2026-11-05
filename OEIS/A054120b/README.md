# OEIS A054120 (second McGarvey conjecture): T(n,k) = A081577(n,k) − A081577(n−2,k−1)

**Source.** OEIS [A054120](https://oeis.org/A054120): triangle with T(n,0) = T(n,n) = 1; T(n,k) is the sum of the
T(i,j) on or between vertical lines through T(n−1,k−1) and T(n−1,k), not below T(n,k). Comment by G. McGarvey
(Sep 20 2007): "Conjecture: T(n,k) = A081577(n,k) - A081577(n-2,k-1). (A081577 is Pascal-(1,2,1) array)."
The first McGarvey conjecture (T(n,k) = T(n−1,k−1) + 2T(n−2,k−1) + T(n−1,k)) was proved in the entry by
R. J. Hendel (2015).

**Reading.** In the centred layout T(i,j) sits at horizontal position 2j − i, so T(n,k) (0 < k < n) is the sum over
rows i < n and 2k−n−1 ≤ 2j−i ≤ 2k−n+1. A081577 is the square array S(a,0) = S(0,b) = 1,
S(a,b) = S(a,b−1) + 2S(a−1,b−1) + S(a−1,b), read as a triangle A081577(n,k) = S(n−k,k) (symmetric), and is 0 outside
0 ≤ k ≤ n.

**Result.** True for all n, k (both sides 0 for k > n).

**Argument.** Let G(n,x) be the sum of T(i,j), i < n, on the vertical line 2j−i = x. For n ≥ 1 and every k,
T(n,k) = G(n,2k−n−1) + G(n,2k−n) + G(n,2k−n+1) (boundary columns checked directly). T(n−2,k−1) uses the same
three lines, so T(n,k) − T(n−2,k−1) is the contribution of rows n−1 and n−2: T(n−1,k−1) + T(n−2,k−1) + T(n−1,k)
(parity kills the other three line/row pairs). This is McGarvey's first recurrence for n ≥ 3, k ≥ 1.
The zero-extended triangle A081577 satisfies the same recurrence at every (n,k) ≠ (0,0), so
D(n,k) = A081577(n,k) − A081577(n−2,k−1) satisfies it except at (0,0), (2,1). T and D agree on rows 0–2
(T(2,1) = 3 = 4 − 1), hence everywhere by induction on n.

**Evidence.**
- Lean (Mathlib): [`A054120b_mathlib.lean`](A054120b_mathlib.lean), with A054120 defined by the
  between-the-lines sum (well-founded recursion). `A054120b_conjecture (n k : ℕ) : (A054120 n k : ℤ) =
  A081577 n k − (if 2 ≤ n ∧ 1 ≤ k then A081577 (n−2) (k−1) else 0)`. Supporting: `A054120_eq_F`, `A054120_rec`
  (Hendel's recurrence), `A081577z_rec`, `A054120b_D_rec`, `A054120b_main`, `A081577_sq_symm`,
  `A054120b_data` (rows 0–7 against the entry). Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: geometric definition vs the formula and the recurrence for n < 40.
- Outside Lean: the reading of the geometric definition.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: OEIS A054120 (Hendel's proof of the first conjecture; R. J. Mathar's 2022 comment
that the triangle appears to be the array with g.f. (1−uv)/(1−u−v−2uv), which is equivalent to this conjecture),
A081577, web search, google-deepmind/formal-conjectures (no file). With Hendel's recurrence the second conjecture is a
short induction; no written proof found.
