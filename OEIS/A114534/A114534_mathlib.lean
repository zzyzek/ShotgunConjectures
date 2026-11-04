/-
OEIS A114534, Mathlib proof.

A114534(n) = permanent of the n × n matrix M filled row by row with the
Fibonacci numbers F(0), F(1), ..., F(n² - 1). Conjecture: the rank of M is 2
for every n ≥ 2.

Main theorem `A114534_main`: for every n ≥ 2, the matrix
`A114534_M n : Matrix (Fin n) (Fin n) ℚ`, M(r, c) = F(r·n + c) (0-based,
`Nat.fib`), has `Matrix.rank` exactly 2. This is the README result.

Proof: M = A·B with A of width 2 (addition formula), so rank ≤ 2; the 2 × 2
submatrix on rows and columns 0, 1 has determinant -F(n) ≠ 0, so rank ≥ 2
(`Matrix.rank_submatrix_le`, `Matrix.rank_of_det_ne_zero`). Nothing is
outside Lean. (The indexing check a(3) = 132 is in the core file.)
-/
import Mathlib

/-- The n × n matrix filled row by row with F(0), F(1), ... -/
def A114534_M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun r c => (Nat.fib (r * n + c) : ℚ)

theorem A114534_add (a c : ℕ) :
    (Nat.fib (a + c) : ℚ) =
      Nat.fib a * ((Nat.fib (c + 1) : ℚ) - Nat.fib c) + Nat.fib (a + 1) * Nat.fib c := by
  rcases c with _ | c
  · simp
  · have h := Nat.fib_add a c
    have h2 : (Nat.fib (c + 2) : ℚ) = Nat.fib (c + 1) + Nat.fib c := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show a + (c + 1) = a + c + 1 by ring, h, show c + 1 + 1 = c + 2 by ring, h2]
    push_cast
    ring

theorem A114534_main (n : ℕ) (hn : 2 ≤ n) : (A114534_M n).rank = 2 := by
  apply le_antisymm
  · let A : Matrix (Fin n) (Fin 2) ℚ := fun r j =>
      if j = 0 then (Nat.fib (r * n) : ℚ) else Nat.fib (r * n + 1)
    let B : Matrix (Fin 2) (Fin n) ℚ := Matrix.of fun j c =>
      if j = 0 then (Nat.fib (c + 1) : ℚ) - Nat.fib c else Nat.fib c
    have hM : A114534_M n = A * B := by
      ext r c
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [A, B, A114534_M, Matrix.of_apply, Fin.isValue, ↓reduceIte, one_ne_zero]
      exact A114534_add _ _
    rw [hM]
    exact (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_width A)
  · let f : Fin 2 → Fin n := fun i => ⟨i, by omega⟩
    have hdet : ((A114534_M n).submatrix f f).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, A114534_M, Matrix.of_apply, f]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, zero_mul, zero_add, one_mul,
        Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one]
      have : (Nat.fib n : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.fib_pos.2 (by omega)).ne'
      intro h
      apply this
      simp only [add_zero] at h
      linarith
    have h1 := Matrix.rank_of_det_ne_zero hdet
    have h2 := Matrix.rank_submatrix_le (A114534_M n) f f
    rw [h1, Fintype.card_fin] at h2
    exact h2
