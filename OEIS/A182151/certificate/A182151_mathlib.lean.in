import OpenProblemsLib

/-
OEIS A182151 (Mathlib). Conjecture (Coman 2012): any Carmichael number C divisible by 31 is
2790n + 31, 2790n + 31² or 2790n + 31·61 with n natural. README result: true.

Main theorem `A182151_main`: for every Carmichael number C (Mathlib `Nat.IsCarmichael`)
with 31 ∣ C there is a natural n with C = 2790n + 31, C = 2790n + 31² or C = 2790n + 31·61.
Proof: Korselt's criterion in the necessary direction (Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, proved there from the cyclicity of (ZMod p)ˣ / the Carmichael function), squarefreeness of Carmichael numbers (Mathlib `Nat.IsCarmichael.squarefree`), and `omega` for the congruences.

Outside Lean: nothing. (Template certificate/A182151_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

theorem A182151_main (C : ℕ) (h : C.IsCarmichael) (h31 : 31 ∣ C) :
    ∃ n, C = 2790 * n + 31 ∨ C = 2790 * n + 31 ^ 2 ∨ C = 2790 * n + 31 * 61 := by
  have h30 : 30 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h31
  have := h.two_lt
  exact ⟨C / 2790, by omega⟩
