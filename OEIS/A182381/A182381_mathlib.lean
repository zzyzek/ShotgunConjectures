import OpenProblemsLib

/-
OEIS A182381 (Mathlib). Conjecture (Coman 2012): any Carmichael number C divisible by 17 and
29 can be written as C = 952n + 561. README result: true.

Main theorem `A182381_main`: for every Carmichael number C (Mathlib `Nat.IsCarmichael`)
with 17 ∣ C and 29 ∣ C there is a natural n with C = 952n + 561.
Proof: Korselt's criterion in the necessary direction (Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, proved there from the cyclicity of (ZMod p)ˣ / the Carmichael function), squarefreeness of Carmichael numbers (Mathlib `Nat.IsCarmichael.squarefree`), and `omega` for the congruences.

Outside Lean: nothing. (Template certificate/A182381_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

theorem A182381_main (C : ℕ) (h : C.IsCarmichael) (h17 : 17 ∣ C) (h29 : 29 ∣ C) :
    ∃ n, C = 952 * n + 561 := by
  have k17 : 16 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h17
  have k29 : 28 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h29
  have := h.two_lt
  exact ⟨C / 952, by omega⟩
