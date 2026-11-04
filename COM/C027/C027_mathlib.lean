import Mathlib

/-
COM-C027 (Mathlib). Coman, conjecture 27: n^E ≡ n (mod 544) for every natural n and every
Euler pseudoprime E. README result: false, n = 2, E = 561 gives 2^561 ≡ 512 (mod 544).

Definition used (`EulerPsp b E`): E is an odd composite number > 1, coprime to b, with
b^((E-1)/2) ≡ J(b | E) (mod E), J the Mathlib Jacobi symbol `jacobiSym`.

Main theorem `C027_main`: 561 is an Euler pseudoprime to base 2 (with J(2 | 561) = 1 from
Mathlib's second supplementary law `jacobiSym.at_two`, 561 ≡ 1 (mod 8)), 2^561 % 544 = 512,
and hence the conjecture `∀ n E, (∃ b, EulerPsp b E) → n^E ≡ n [MOD 544]` is false.
Under the weaker definition b^((E-1)/2) ≡ ±1 (mod E) the same witness works, since
2^280 ≡ 1 (mod 561) is part of the proof.

Outside Lean: nothing.
-/

/-- Euler pseudoprime to base `b`. -/
def EulerPsp (b E : ℕ) : Prop :=
  Odd E ∧ 1 < E ∧ ¬ E.Prime ∧ Nat.Coprime b E ∧
    ((b : ℤ) ^ ((E - 1) / 2) ≡ jacobiSym b E [ZMOD E])

theorem jacobi_two_561 : jacobiSym 2 561 = 1 := by
  have h := jacobiSym.at_two (b := 561) (by decide)
  rw [h]
  have : ((561 : ℕ) : ZMod 8) = 1 := by decide
  rw [this]
  rfl

theorem C027_euler : EulerPsp 2 561 := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 : jacobiSym ((2 : ℕ) : ℤ) 561 = ((1 : ℕ) : ℤ) := jacobi_two_561
  rw [h1, ← Nat.cast_pow, Int.natCast_modEq_iff]
  unfold Nat.ModEq
  decide +kernel

theorem C027_main :
    EulerPsp 2 561 ∧ 2 ^ 561 % 544 = 512 ∧
      ¬ ∀ n E : ℕ, (∃ b, EulerPsp b E) → n ^ E ≡ n [MOD 544] := by
  refine ⟨C027_euler, by decide +kernel, fun h => ?_⟩
  have := h 2 561 ⟨2, C027_euler⟩
  unfold Nat.ModEq at this
  have h2 : 2 ^ 561 % 544 = 512 := by decide +kernel
  omega
