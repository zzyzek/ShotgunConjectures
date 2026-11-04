import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

/-!
# Binary modular exponentiation for kernel computation

`Nat.pow` with a large exponent is not accelerated in the kernel, so `a ^ e % m`
cannot be evaluated by `decide +kernel` once `e` is large. `powMod a e m` computes
the same number by square-and-multiply, using only `*`, `%`, `/` on literals
(all GMP-accelerated in the kernel). The recursion is structural on a fuel
argument equal to `e`; the exponent halves each step, so the kernel unfolds it
about `log2 e` times.

Main result: `powMod_eq : powMod a e m = a ^ e % m`.
-/

namespace OpenProblemsLib

/-- Square-and-multiply loop: `powModAux m fuel b e acc = acc * b ^ e % m` when `e ≤ fuel`. -/
def powModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc % m
  | fuel + 1, b, e, acc =>
    if e = 0 then acc % m
    else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

/-- `powMod a e m = a ^ e % m`, computed by binary exponentiation. -/
def powMod (a e m : ℕ) : ℕ := powModAux m e (a % m) e 1

theorem powModAux_eq (m : ℕ) : ∀ (fuel b e acc : ℕ), e ≤ fuel →
    powModAux m fuel b e acc = acc * b ^ e % m
  | 0, b, e, acc, h => by
    have : e = 0 := by omega
    subst this; simp [powModAux]
  | fuel + 1, b, e, acc, h => by
    simp only [powModAux]
    by_cases he : e = 0
    · subst he; simp
    · simp only [he, ↓reduceIte]; rw [powModAux_eq m fuel _ _ _ (by omega)]
      have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
        rw [← pow_two, ← pow_mul, ← pow_add, Nat.div_add_mod]
      have h2 : Nat.ModEq m ((b * b % m) ^ (e / 2)) ((b * b) ^ (e / 2)) := (Nat.mod_modEq _ _).pow _
      by_cases ho : e % 2 = 1
      · simp only [ho, ↓reduceIte]
        have h1 : Nat.ModEq m (acc * b % m) (acc * b) := Nat.mod_modEq _ _
        have h3 := h1.mul h2
        rw [hsplit, ho, pow_one]
        unfold Nat.ModEq at h3
        rw [h3]; congr 1; ring
      · have h0 : e % 2 = 0 := by omega
        simp only [ho, ↓reduceIte]
        have h3 := (Nat.ModEq.refl acc).mul h2
        rw [hsplit, h0, pow_zero, mul_one]
        exact h3

theorem powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  unfold powMod
  rw [powModAux_eq m e _ e 1 le_rfl, one_mul, ← Nat.pow_mod]

end OpenProblemsLib
