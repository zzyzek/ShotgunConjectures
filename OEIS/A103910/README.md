# OEIS A103910: rows of the inverse Fibonomial triangle sum to zero

**Source.** [A103910](https://oeis.org/A103910), triangle T read by rows: inverse of the Fibonomial triangle
[A010048](https://oeis.org/A010048). Comment: "Conjecture: all rows except the first add to zero." (OEIS text,
CC BY-SA 4.0, entry as of Jul 05 2026, checked 2026-11-07.)

**Result.** True (known): row n of T sums to 1 for n = 0 and to 0 for n >= 1.

**Argument.** Column 0 of the Fibonomial triangle A is all ones (empty products), so A e_0 = 1 (the all-ones
vector). Hence T 1 = T A e_0 = e_0. A is lower unitriangular (A(n,n) = 1), so T exists and its first N+1 rows are
the inverse of the (N+1) x (N+1) truncation of A.

**Evidence.**
- Lean (Mathlib): [`A103910_mathlib.lean`](A103910_mathlib.lean). `rowsum_of_left_inv`: any T with
  T * Fib N = 1 has row sums 1, 0, 0, ...; `A103910_rowsum`: the same for (Fib N)⁻¹ (`det_Fib`: det = 1).
  `Fib N` uses A010048(n,k) = prod_{i<k} F(n-i) / prod_{i<k} F(i+1). Axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: inverts rows 0..30, matches the 55 data terms, row sums 1, 0, 0, ...
- Outside Lean: none beyond the definition of A010048 (only its column 0 and diagonal enter the proof).

**Review level.** `lean-proof`.

**Prior art.** Known: P. Bala's formula block in the entry (Jun 30 2026) derives the row sums from the generating
function 1/E(z) * E(xz) (generalized Riordan array of Wang and Wang, Discrete Math. 308 (2008) 6466-6500); the
comment was left labelled "Conjecture". The two-line matrix argument above is the same fact without generating
functions. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (checked 2026-11-07).
