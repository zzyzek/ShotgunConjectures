# OEIS A078537: row sums of A078536 are the partitions of 4^n into powers of 4

**Source.** [A078537](https://oeis.org/A078537) (Paul D. Hanna, 2002): number of partitions of 4^n into powers of 4.
"Conjecture: a(n) = sum of the n-th row of lower triangular matrix A078536." [A078536](https://oeis.org/A078536):
the infinite lower triangular matrix M with [M^4](i,j) = M(i+1,j+1), "M(0,k)=1 and M(k,k)=1"; the entry also
conjectures M(n,k) = [x^(4^n - 4^(n-k))] 1/Prod_{j=0..n-k}(1 - x^(4^j)) for 0 <= k < n. (OEIS text, revisions #21 of
Nov 28 2017 and #10 of Oct 20 2019, checked 2026-11-06.)

**Reading.** "M(0,k)=1" read as M(k,0) = 1 (column 0; the entry's data and Mathematica program use this). The
matrix product of lower-triangular infinite matrices is the finite sum over l <= i.

**Result.** True, for every base q >= 2 (q = 4 here; q = 2, 3 are A078121, A078122). Write t(m, c) for the number
of partitions of c q^m into 1, q, ..., q^m. Then M(n,k) = t(n-k, q^k - 1) (the entry's conjectured formula), more
generally [M^s](n,k) = t(n-k, s q^k - 1) for s >= 1, and row n sums to the number of partitions of q^n into powers of q.

**Argument.**
1. *Convolution identity.* For A >= 1, b >= 0: sum_{j=0..m} t(m-j, A q^j - 1) t(j, b) = t(m, A + b). Induction on m and
   b, using t(m+1, c+1) = t(m+1, c) + t(m, q(c+1)) and t(0, c) = 1. For b = 0 it reads
   sum_j t(m-j, A q^j - 1) = t(m, A) (classify partitions of A q^m by the largest part).
2. *Powers.* Let P_s(n,k) = t(n-k, s q^k - 1). With A = q^k and b = s q^k - 1, step 1 gives P_1 P_s = P_(s+1).
   Hence P_1^q = P_q, and P_q(i,j) = t(i-j, q^(j+1) - 1) = P_1(i+1, j+1); also P_1(n,0) = P_1(n,n) = 1.
3. *Uniqueness.* The defining relations fix row i+1 from rows <= i, so A078536 = P_1.
4. *Row sum.* sum_k t(n-k, q^k - 1) = t(n, 1) by the b = 0 case with A = 1, and t(n, 1) counts partitions of q^n into
   powers of q (parts are <= q^n).

**Evidence.**
- Lean (Mathlib): [`A078537_mathlib.lean`](A078537_mathlib.lean), namespace `A078537`. Main theorem `A078537_conj`:
  any `M : ℕ → ℕ → ℤ` with `M i j = 0` for i < j, `M i 0 = 1` and `mm4 M i j = M (i+1) (j+1)` has
  `∑ k ∈ range (n+1), M n k = a n`, where `a n` counts `Nat.Partition (4^n)` with all parts powers of 4 (the OEIS
  definition). Also `A078536_formula` (M n k = t 4 (n-k) (4^k - 1)) and `A078536_exists` (the candidate satisfies all
  defining properties, including M(k,k) = 1). Route: `conv`, `sum_one`, `left_mul`, `P4`, `M_eq`, `ways_Lq`, `a_eq_t`
  (the multiset/coin-change bridge is copied from OEIS/A078128). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): builds the matrices from the definition (q = 2, 3, 4, 9 rows),
  checks M(n,k) = t(n-k, q^k - 1), the identity of step 1 on a grid, and the row sums against A078537(0..8).
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data terms (check.py); the q = 2, 3 cases
  (the Lean file fixes q = 4 in `mm4`; the lemmas `conv`, `left_mul` are for general q).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: A078537, A078536, A078122 still say "conjecture"; A078121 (q = 2) gives the column
formulas and a recurrence (Kurkov 2025) and a MathOverflow answer on its diagonals, not this identity. Web search found
no proof. Not in google-deepmind/formal-conjectures (clone of 2026-11-06) or otoi-lab/oeis-lean-proofs (clone of
2026-10-13). The semigroup formula [M^s](n,k) = t(n-k, s q^k - 1) and the convolution identity are ours.
