import OpenProblemsLib

/-
OEIS A182515 (Mathlib). Conjecture (Coman 2012): any Carmichael number C divisible by 23 and
67 can be written as C = 23·67·(66n + 23). README result: true (with n ≥ 1).

Main theorem `A182515_main`: for every Carmichael number C (Mathlib `Nat.IsCarmichael`)
with 23 ∣ C and 67 ∣ C there is n ≥ 1 with C = 23·67·(66n + 23).
Proof: Korselt's criterion in the necessary direction (Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, proved there from the cyclicity of (ZMod p)ˣ / the Carmichael function), squarefreeness of Carmichael numbers (Mathlib `Nat.IsCarmichael.squarefree`), and `omega` for the congruences.

Outside Lean: nothing. (Template certificate/A182515_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- A Carmichael number is not divisible by p² (p > 1). -/
theorem not_sq_dvd (C p : ℕ) (h : C.IsCarmichael) (hp : 1 < p) : ¬ p * p ∣ C := by
  intro hd
  have hu : IsUnit p := h.squarefree p hd
  rw [Nat.isUnit_iff] at hu
  omega

theorem A182515_main (C : ℕ) (h : C.IsCarmichael) (h23 : 23 ∣ C) (h67 : 67 ∣ C) :
    ∃ n, 1 ≤ n ∧ C = 23 * 67 * (66 * n + 23) := by
  have k67 : 66 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h67
  have sq := not_sq_dvd C 23 h (by norm_num)
  have := h.two_lt
  obtain ⟨m, rfl⟩ : 23 * 67 ∣ C := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h23 h67
  have hm : m % 66 = 23 := by omega
  have hm23 : m ≠ 23 := by
    rintro rfl; exact sq (by norm_num)
  exact ⟨(m - 23) / 66, by omega, by omega⟩

