import Mathlib

/-
OEIS A158233 (offset 1): a(n) = A120070(n+1)*A120070(n+2) mod 9, where
A120070 (offset 2) is the triangle T(m,l) = m^2 - l^2, 1 <= l <= m-1, read
by rows: 3, 8, 5, 15, 12, 7, ...
Conjecture (entry): a(n) only takes the values 0, 3, 4, 6.

Definitions.  `pos i` is the cell (m, l) of the i-th term of A120070, by the
same walk as the entry's Maple program: pos 2 = (2, 1); the next cell is
(m, l+1) if l+1 <= m-1, else (m+1, 1).  `A120070 i = m^2 - l^2`,
`A158233 n = (A120070 (n+1) * A120070 (n+2)) % 9`.

Main theorem.
* `A158233_values`: for n >= 1, A158233 n is 0, 3, 4 or 6.
* `A158233_attained`: each of the four values occurs (n = 1, 2, 3, 4).

Route.  Inside a row the product is (m^2-l^2)(m^2-(l+1)^2), across rows it is
(2l+1)((l+2)^2-1); both reduce in ZMod 9 to a function of m, l mod 9, and
`key_row`, `key_cross` check all residues by `decide`.

Not checked in this file: agreement of `A158233` with the OEIS data terms
(certificate/check.py compares 5000 terms).
-/

namespace OEIS158233

/-- Cell (m, l) of the i-th term (i ≥ 2) of A120070, rows read left to right. -/
def pos : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | 1 => (2, 1)
  | 2 => (2, 1)
  | (i + 3) =>
    let p := pos (i + 2)
    if p.2 + 1 < p.1 then (p.1, p.2 + 1) else (p.1 + 1, 1)

/-- A120070 read by rows (offset 2): T(m, l) = m^2 - l^2. -/
def A120070 (i : ℕ) : ℕ := (pos i).1 ^ 2 - (pos i).2 ^ 2

/-- A158233 (offset 1). -/
def A158233 (n : ℕ) : ℕ := (A120070 (n + 1) * A120070 (n + 2)) % 9

theorem pos_inv (i : ℕ) : 1 ≤ (pos i).2 ∧ (pos i).2 < (pos i).1 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ => simp [pos]
    | 1, _ => simp [pos]
    | 2, _ => simp [pos]
    | (j + 3), ih =>
      have h := ih (j + 2) (by omega)
      simp only [pos]
      split_ifs with hc
      · exact ⟨by omega, hc⟩
      · exact ⟨le_refl _, by omega⟩

theorem key_row : ∀ x y : ZMod 9,
    ((x ^ 2 - y ^ 2) * (x ^ 2 - (y + 1) ^ 2)).val ∈ ({0, 3, 4, 6} : Finset ℕ) := by
  decide

theorem key_cross : ∀ y : ZMod 9,
    (((y + 1) ^ 2 - y ^ 2) * ((y + 2) ^ 2 - 1 ^ 2)).val ∈ ({0, 3, 4, 6} : Finset ℕ) := by
  decide

theorem cast_sq_sub {m l : ℕ} (h : l < m) :
    ((m ^ 2 - l ^ 2 : ℕ) : ZMod 9) = (m : ZMod 9) ^ 2 - (l : ZMod 9) ^ 2 := by
  rw [Nat.cast_sub (Nat.pow_le_pow_left h.le 2)]
  push_cast
  ring

theorem A158233_values (n : ℕ) (hn : 1 ≤ n) :
    A158233 n = 0 ∨ A158233 n = 3 ∨ A158233 n = 4 ∨ A158233 n = 6 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hv : A158233 (k + 1) ∈ ({0, 3, 4, 6} : Finset ℕ) := by
    have hp := pos_inv (k + 2)
    have hnext : pos (k + 3) =
        (if (pos (k + 2)).2 + 1 < (pos (k + 2)).1
          then ((pos (k + 2)).1, (pos (k + 2)).2 + 1)
          else ((pos (k + 2)).1 + 1, 1)) := by
      simp [pos]
    have hval : A158233 (k + 1) =
        (((A120070 (k + 2) * A120070 (k + 3) : ℕ) : ZMod 9)).val := by
      rw [ZMod.val_natCast]; rfl
    rw [hval]
    unfold A120070
    rw [hnext]
    generalize pos (k + 2) = q at hp ⊢
    obtain ⟨m, l⟩ := q
    simp only at hp ⊢
    split_ifs with hc
    · simp only
      rw [Nat.cast_mul, cast_sq_sub hp.2, cast_sq_sub hc]
      push_cast
      exact key_row _ _
    · obtain rfl : m = l + 1 := by omega
      simp only
      rw [Nat.cast_mul, cast_sq_sub hp.2, cast_sq_sub (show 1 < l + 1 + 1 by omega)]
      push_cast
      have := key_cross (l : ZMod 9)
      convert this using 4
      ring
  simpa using hv

theorem A158233_attained :
    A158233 1 = 6 ∧ A158233 2 = 4 ∧ A158233 3 = 3 ∧ A158233 4 = 0 := by
  decide

