import OpenProblemsLib

/-
OEIS A182206 (Mathlib). Conjecture (Coman 2012): any Carmichael number C divisible by 37 and
73 can be written as C = 37·73·(18n + 91) with n natural. README result: true (with n ≥ 1).

Main theorem `A182206_main`: for every Carmichael number C (Mathlib `Nat.IsCarmichael`)
with 37 ∣ C and 73 ∣ C there is n ≥ 1 with C = 37·73·(18n + 91).
Proof: Korselt's criterion in the necessary direction (Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, proved there from the cyclicity of (ZMod p)ˣ / the Carmichael function), squarefreeness of Carmichael numbers (Mathlib `Nat.IsCarmichael.squarefree`), and `omega` for the congruences.

Outside Lean: nothing. (Template certificate/A182206_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- A Carmichael number is not divisible by p² (p > 1). -/
theorem not_sq_dvd (C p : ℕ) (h : C.IsCarmichael) (hp : 1 < p) : ¬ p * p ∣ C := by
  intro hd
  have hu : IsUnit p := h.squarefree p hd
  rw [Nat.isUnit_iff] at hu
  omega

theorem A182206_main (C : ℕ) (h : C.IsCarmichael) (h37 : 37 ∣ C) (h73 : 73 ∣ C) :
    ∃ n, 1 ≤ n ∧ C = 37 * 73 * (18 * n + 91) := by
  have k37 : 36 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h37
  have k73 : 72 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h73
  have sq := not_sq_dvd C 37 h (by norm_num)
  have := h.two_lt
  have e1 : 1 ≤ (C / 2701 - 91) / 18 := by omega
  have e2 : C = 37 * 73 * (18 * ((C / 2701 - 91) / 18) + 91) := by omega
  exact ⟨_, e1, e2⟩
