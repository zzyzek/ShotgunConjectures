/-
OEIS A214449, Mathlib proof.

A214449(n) = least m > 0 with n! ≤ m^m (offset 1). A118168(n) = the x
minimizing |x^x - n!| (offset 0). Conjecture: A214449 is A118168 with the
first two 1s deleted, i.e. A214449(n) = A118168(n + 1) for n ≥ 1.

Main theorem `A214449_main`:
* `A214449 188 = 159`, with `A214449 n` defined as `Nat.find` of
  "∃ m > 0, n! ≤ m^m";
* 158 is the unique natural number x minimizing |x^x - 189!| (as integers):
  every x ≠ 158 has a strictly larger distance.
So A214449(188) = 159 ≠ 158 = A118168(189), and the conjecture is false
whatever tie-breaking rule A118168 uses (there is no tie at 189).
This is the README result (first mismatch at n = 188 is not claimed here;
the README lists it from the certificate script and it is not part of the
disproof).

Monotonicity of x ↦ x^x is proved here. Nothing is outside Lean.
-/
import Mathlib

/-- A214449(n): least m > 0 with n! ≤ m^m. -/
def A214449 (n : ℕ) : ℕ :=
  Nat.find (⟨Nat.factorial n, Nat.factorial_pos n, by
    rcases Nat.lt_or_ge (Nat.factorial n) 2 with h | h
    · calc Nat.factorial n ≤ 1 := by omega
        _ ≤ Nat.factorial n ^ Nat.factorial n := Nat.one_le_pow _ _ (Nat.factorial_pos n)
    · calc Nat.factorial n = Nat.factorial n ^ 1 := (pow_one _).symm
        _ ≤ Nat.factorial n ^ Nat.factorial n := Nat.pow_le_pow_right (Nat.factorial_pos n) (by omega)⟩ :
    ∃ m, 0 < m ∧ Nat.factorial n ≤ m ^ m)

/-- x ↦ x^x is monotone on ℕ (with 0^0 = 1). -/
theorem A214449_selfpow_mono {y z : ℕ} (h : y ≤ z) : y ^ y ≤ z ^ z := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp
    · simpa using Nat.one_le_pow z z hz
  · calc y ^ y ≤ z ^ y := Nat.pow_le_pow_left h y
      _ ≤ z ^ z := Nat.pow_le_pow_right (by omega) h

theorem A214449_selfpow_strict {y z : ℕ} (h : y < z) (hz : 2 ≤ z) : y ^ y < z ^ z := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp only [pow_zero]
    calc 1 < 2 ^ z := Nat.one_lt_two_pow (by omega)
      _ ≤ z ^ z := Nat.pow_le_pow_left hz z
  · calc y ^ y < z ^ y := Nat.pow_lt_pow_left h (by omega)
      _ ≤ z ^ z := Nat.pow_le_pow_right (by omega) h.le

theorem A214449_facts : 158 ^ 158 < Nat.factorial 188 ∧ Nat.factorial 188 ≤ 159 ^ 159 ∧
    158 ^ 158 < Nat.factorial 189 ∧ Nat.factorial 189 < 159 ^ 159 ∧
    Nat.factorial 189 - 158 ^ 158 < 159 ^ 159 - Nat.factorial 189 := by
  decide +kernel

/-- Integer form of the nearness comparison, for abstract A < F < B. -/
theorem A214449_near (A B F X : ℕ) (h3 : A < F) (h4 : F < B) (h5 : F - A < B - F)
    (hX : X < A ∨ B ≤ X) : |(A : ℤ) - F| < |(X : ℤ) - F| := by
  rw [abs_of_neg (by omega)]
  rcases hX with hX | hX
  · rw [abs_of_neg (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

theorem A214449_main :
    A214449 188 = 159 ∧
    ∀ x : ℕ, x ≠ 158 →
      |((158 ^ 158 : ℕ) : ℤ) - (Nat.factorial 189 : ℕ)| <
        |((x ^ x : ℕ) : ℤ) - (Nat.factorial 189 : ℕ)| := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := A214449_facts
  refine ⟨?_, ?_⟩
  · rw [A214449, Nat.find_eq_iff]
    refine ⟨⟨by norm_num, f2⟩, fun m hm ⟨hm0, hmf⟩ => ?_⟩
    have := A214449_selfpow_mono (show m ≤ 158 by omega)
    generalize (158 : ℕ) ^ 158 = A at *
    generalize m ^ m = M at *
    generalize Nat.factorial 188 = F at *
    omega
  · intro x hx
    apply A214449_near _ (159 ^ 159) _ _ f3 f4 f5
    rcases Nat.lt_or_gt_of_ne hx with hlt | hgt
    · exact Or.inl (A214449_selfpow_strict hlt (by norm_num))
    · exact Or.inr (A214449_selfpow_mono (show 159 ≤ x by omega))
