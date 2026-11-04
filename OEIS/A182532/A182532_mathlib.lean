import OpenProblemsLib

/-
OEIS A182532 (Mathlib). Conjectures (1)-(4) (Coman 2012): a Carmichael number C divisible by
7 and 17 is 7·17·(120n + 119) if C ≡ 1 (mod 10), 7·17·(120n + 95) if C ≡ 5, 7·17·(120n + 47)
if C ≡ 3, and 7·17·(120n + 71) if C ≡ 9 (mod 10). README result: true.

Main theorem `A182532_main`: the four implications, for every Carmichael number C (Mathlib
`Nat.IsCarmichael`) with 7 ∣ C and 17 ∣ C, with n natural.
Proof: Korselt's criterion in the necessary direction (Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, proved there from the cyclicity of (ZMod p)ˣ / the Carmichael function), squarefreeness of Carmichael numbers (Mathlib `Nat.IsCarmichael.squarefree`), and `omega` for the congruences.

Outside Lean: nothing. (Template certificate/A182532_mathlib.lean.in, tools/lean_expand.py.)
-/

open OpenProblemsLib

theorem A182532_main (C : ℕ) (h : C.IsCarmichael) (h7 : 7 ∣ C) (h17 : 17 ∣ C) :
    (C % 10 = 1 → ∃ n, C = 7 * 17 * (120 * n + 119)) ∧
    (C % 10 = 5 → ∃ n, C = 7 * 17 * (120 * n + 95)) ∧
    (C % 10 = 3 → ∃ n, C = 7 * 17 * (120 * n + 47)) ∧
    (C % 10 = 9 → ∃ n, C = 7 * 17 * (120 * n + 71)) := by
  have k7 : 6 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h7
  have k17 : 16 ∣ C - 1 := by simpa using korselt_necessary h (by norm_num) h17
  have := h.two_lt
  refine ⟨fun _ => ⟨C / 14280, by omega⟩, fun _ => ⟨C / 14280, by omega⟩,
    fun _ => ⟨C / 14280, by omega⟩, fun _ => ⟨C / 14280, by omega⟩⟩
