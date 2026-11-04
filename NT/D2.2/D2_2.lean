/-
NT-D2.2 (Guy, UPINT 3rd ed., D2): "prove that x^n + y^n = n! z^n has no
integer solutions with n > 2".  False for n = 3.

Checked here (core Lean, no Mathlib): `nt_d2_2`: 17^3 + 37^3 = 3! · 21^3
(taken from ../open-problems/lean/Witnesses1.lean).
Not checked here: the cases n ≥ 4 (n = 4 has no nontrivial solution by
2-adic descent, see README; n ≥ 5 is not addressed).
-/

theorem nt_d2_2 : 17 ^ 3 + 37 ^ 3 = (3 * 2 * 1) * 21 ^ 3 := by decide
