import Mathlib

/-!
# OEIS A069187: core(k) = ceiling(sqrt(k)) exactly for k = 1 and k = n^2 (n^2+1) with n^2+1 squarefree

* `core k`: the least `s ≥ 1` with `k s` a square (OEIS definition of the squarefree part).
* `InA069187 k`: `k ≥ 1` and `core k = ⌈√k⌉`, written as `k ≤ (core k)^2 ∧ (core k - 1)^2 < k`.

Checked: `A069187_main` (for `k ≥ 1`: `core k = ⌈√k⌉₊ ↔ k = 1 ∨ ∃ n ≥ 1, Squarefree (n^2+1) ∧
k = n^2 (n^2+1)`), via `A069187_iff` and `ceil_sqrt_iff`.
So the comment (A071253 minus the indices in A049532) holds except that the first term is 1, not
A071253(0) = 0.
Not checked: nothing beyond the reading of the OEIS definition.
-/

namespace A069187

theorem core_ex (k : ℕ) : ∃ s, 1 ≤ s ∧ IsSquare (k * s) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, le_rfl, ⟨0, by simp⟩⟩
  · exact ⟨k, hk, ⟨k, rfl⟩⟩

open Classical in
noncomputable def core (k : ℕ) : ℕ := Nat.find (core_ex k)

def InA069187 (k : ℕ) : Prop := 1 ≤ k ∧ k ≤ core k ^ 2 ∧ (core k - 1) ^ 2 < k

theorem dvd_of_sq (a s c : ℕ) (ha : Squarefree a) (h : a * s = c * c) : a ∣ s := by
  have h1 : a ∣ c ^ 2 := ⟨s, by rw [sq, ← h]⟩
  have h2 : a ∣ c := (ha.dvd_pow_iff_dvd (by norm_num)).mp h1
  obtain ⟨d, rfl⟩ := h2
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · exact absurd ha not_squarefree_zero
  · have : s = a * (d * d) := by
      have := h; nlinarith [this]
    exact ⟨d * d, this⟩

theorem core_eq (a b : ℕ) (ha : Squarefree a) (hb : 1 ≤ b) : core (b ^ 2 * a) = a := by
  have ha1 : 1 ≤ a := Nat.pos_of_ne_zero (fun h => by simp [h] at ha)
  unfold core
  rw [Nat.find_eq_iff]
  refine ⟨⟨ha1, ⟨b * a, by ring⟩⟩, ?_⟩
  rintro s hs ⟨hs1, c, hc⟩
  have hbc : b ^ 2 ∣ c * c := ⟨a * s, by rw [← hc]; ring⟩
  rw [← sq] at hbc
  obtain ⟨e, rfl⟩ := (Nat.pow_dvd_pow_iff (by norm_num)).mp hbc
  have h2 : a * s = e * e := by
    have hb2 : 0 < b ^ 2 := by positivity
    have : b ^ 2 * (a * s) = b ^ 2 * (e * e) := by rw [← mul_assoc, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hb2 this
  have := Nat.le_of_dvd hs1 (dvd_of_sq a s e ha h2)
  omega

theorem A069187_iff (k : ℕ) :
    InA069187 k ↔ k = 1 ∨ ∃ n, 1 ≤ n ∧ Squarefree (n ^ 2 + 1) ∧ k = n ^ 2 * (n ^ 2 + 1) := by
  constructor
  · rintro ⟨hk, h1, h2⟩
    obtain ⟨a, b, ha1, hb, hba, ha⟩ := Nat.sq_mul_squarefree_of_pos hk
    rw [← hba, core_eq a b ha hb] at h1 h2
    have hle : b ^ 2 ≤ a := by
      have : b ^ 2 * a ≤ a * a := by nlinarith
      exact Nat.le_of_mul_le_mul_right this ha1
    have hlt : a ≤ b ^ 2 + 1 := by
      by_contra hc
      have h3 : b ^ 2 * a ≤ (a - 2) * a := Nat.mul_le_mul_right a (by omega)
      have h4 : (a - 2) * a < (a - 1) ^ 2 := by
        obtain ⟨t, rfl⟩ : ∃ t, a = t + 2 := ⟨a - 2, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [show t + 2 - 1 = t + 1 by omega]; nlinarith
      omega
    rcases Nat.eq_or_lt_of_le hle with h | h
    · left
      rw [← h] at ha
      have hb1 : b = 1 := by
        by_contra hb1
        have := (Nat.squarefree_pow_iff hb1 (by norm_num)).mp ha
        omega
      subst hb1
      rw [← hba, ← h]; norm_num
    · right
      have : a = b ^ 2 + 1 := by omega
      subst this
      exact ⟨b, hb, ha, hba.symm⟩
  · rintro (rfl | ⟨n, hn, hsq, rfl⟩)
    · have : core 1 = 1 := by simpa using core_eq 1 1 squarefree_one le_rfl
      refine ⟨le_rfl, ?_, ?_⟩ <;> rw [this] <;> norm_num
    · rw [InA069187, core_eq (n ^ 2 + 1) n hsq hn]
      have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
      refine ⟨by nlinarith, by nlinarith, ?_⟩
      rw [Nat.add_sub_cancel]; nlinarith

theorem ceil_sqrt_iff (k t : ℕ) (ht : 1 ≤ t) :
    ⌈Real.sqrt k⌉₊ = t ↔ (t - 1) ^ 2 < k ∧ k ≤ t ^ 2 := by
  rw [Nat.ceil_eq_iff (by omega)]
  have h0 : (0 : ℝ) ≤ ((t - 1 : ℕ) : ℝ) := by positivity
  rw [Real.lt_sqrt h0, Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem core_pos (k : ℕ) : 1 ≤ core k := (Nat.find_spec (core_ex k)).1

/-- The OEIS definition verbatim: `core(k) = ⌈√k⌉`. -/
theorem A069187_main (k : ℕ) (hk : 1 ≤ k) :
    core k = ⌈Real.sqrt k⌉₊ ↔
      k = 1 ∨ ∃ n, 1 ≤ n ∧ Squarefree (n ^ 2 + 1) ∧ k = n ^ 2 * (n ^ 2 + 1) := by
  rw [← A069187_iff, InA069187, eq_comm, ceil_sqrt_iff k (core k) (core_pos k)]
  tauto
