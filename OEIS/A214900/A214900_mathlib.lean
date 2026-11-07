/-
OEIS A214900: number of ordered representations n = x^2 + y^2 + z^2 + w^4.
Conjecture (Sun, 2012): a(n) ≠ 0 for all n.

Checked here (Mathlib + OpenProblemsLib.ThreeSquares): `A214900_main`, for every n there are
x, y, z, w with n = x^2 + y^2 + z^2 + w^4, unconditionally. The reduction is the one in the
core file A214900.lean (w = 0 unless n = 4^a (8b+7); w = 1 for a = 0, 1; descent n = 16m for
a ≥ 2); Legendre's three-square theorem is `OpenProblemsLib.ThreeSquares.sum_three_sq_iff`.
Not checked here: nothing outside Lean.
-/
import Mathlib
import OpenProblemsLib.ThreeSquares

def A214900_excluded (m : Nat) : Prop := ∃ a b, m = 4 ^ a * (8 * b + 7)

theorem A214900_mod4_of_pos_pow (c k : Nat) : (4 ^ (c + 1) * k) % 4 = 0 := by
  rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_comm _ 4]
  exact Nat.mul_mod_right 4 _

theorem A214900_not_excl_8b6 (b : Nat) : ¬ A214900_excluded (8 * b + 6) := by
  rintro ⟨c, d, h⟩
  cases c with
  | zero => simp at h; omega
  | succ c => have := A214900_mod4_of_pos_pow c (8 * d + 7); omega

theorem A214900_not_excl_32b27 (b : Nat) : ¬ A214900_excluded (32 * b + 27) := by
  rintro ⟨c, d, h⟩
  cases c with
  | zero => simp at h; omega
  | succ c => have := A214900_mod4_of_pos_pow c (8 * d + 7); omega

/-- Legendre's theorem, hard direction, from the library. -/
theorem A214900_legendre (m : Nat) (h : ¬ A214900_excluded m) :
    ∃ x y z : Nat, m = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨x, y, z, h'⟩ := (OpenProblemsLib.ThreeSquares.sum_three_sq_iff m).mpr h
  exact ⟨x, y, z, h'.symm⟩

theorem A214900_main : ∀ n : Nat, ∃ x y z w : Nat, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 4 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hex : A214900_excluded n
    · obtain ⟨a, b, hab⟩ := hex
      match a, hab with
      | 0, hab =>
        obtain ⟨x, y, z, h⟩ := A214900_legendre (8 * b + 6) (A214900_not_excl_8b6 b)
        exact ⟨x, y, z, 1, by simp at hab; omega⟩
      | 1, hab =>
        obtain ⟨x, y, z, h⟩ := A214900_legendre (32 * b + 27) (A214900_not_excl_32b27 b)
        exact ⟨x, y, z, 1, by simp at hab; omega⟩
      | a + 2, hab =>
        have e : n = 16 * (4 ^ a * (8 * b + 7)) := by
          rw [hab, Nat.pow_add, Nat.mul_comm (4 ^ a) (4 ^ 2), Nat.mul_assoc]
        have hpos : 0 < 4 ^ a * (8 * b + 7) := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
        obtain ⟨x, y, z, w, h⟩ := ih (4 ^ a * (8 * b + 7)) (by omega)
        refine ⟨4 * x, 4 * y, 4 * z, 2 * w, ?_⟩
        rw [e, h]
        ring
    · obtain ⟨x, y, z, h⟩ := A214900_legendre n hex
      exact ⟨x, y, z, 0, by simp [h]⟩
