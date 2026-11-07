import Mathlib

/-
Guy, UPINT F31 (Selfridge-Lacampagne, last question): which integers k are quotients a / b of
positive integers a, b whose base-3 digits are all 0 or 1?

Checked here (`interval_obstruction`): if 3·3^m < 2k < 4·3^m for some m (k strictly between
1.5·3^m and 2·3^m), then k is not such a quotient. Also `not_quotient_of_mod3`: k ≡ 2 (mod 3) is
never a quotient (strip factors 3 from b; then k·b ends in digit 2).
Not checked here: the sporadic further non-quotients 529, 592, 601, 616, 5368 (carry-automaton
search, certificate/f313.py), and the absence of other exceptions below 20000.
-/

namespace NT_F31_3

/-- All base-3 digits of a are 0 or 1. -/
def D01 (a : ℕ) : Prop := ∀ d ∈ Nat.digits 3 a, d ≤ 1

/-- k is a quotient of two positive integers with base-3 digits in {0, 1}. -/
def IsQuot (k : ℕ) : Prop := ∃ a b : ℕ, D01 a ∧ D01 b ∧ 0 < b ∧ a = k * b

theorem two_mul_lt (a : ℕ) (h : D01 a) : 2 * a < 3 ^ (Nat.digits 3 a).length := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hd : Nat.digits 3 a = a % 3 :: Nat.digits 3 (a / 3) := Nat.digits_def' (by norm_num) ha
      have h0 : a % 3 ≤ 1 := h _ (by rw [hd]; exact List.mem_cons_self ..)
      have h1 : D01 (a / 3) := fun d hdm => h d (by rw [hd]; exact List.mem_cons_of_mem _ hdm)
      have := ih (a / 3) (Nat.div_lt_self ha (by norm_num)) h1
      rw [hd, List.length_cons, pow_succ]
      omega

theorem pow_le (a : ℕ) (ha : 0 < a) : 3 ^ (Nat.digits 3 a).length ≤ 3 * a :=
  Nat.base_pow_length_digits_le 3 a (by norm_num) ha.ne'

/-- No quotient lies strictly between 1.5·3^m and 2·3^m. -/
theorem interval_obstruction (k m : ℕ) (h1 : 3 * 3 ^ m < 2 * k) (h2 : k < 2 * 3 ^ m) :
    ¬ IsQuot k := by
  rintro ⟨a, b, ha, hb, hb0, rfl⟩
  have hk : 0 < k := by omega
  have ua := two_mul_lt _ ha
  have ub := two_mul_lt _ hb
  have la := pow_le (k * b) (Nat.mul_pos hk hb0)
  have lb := pow_le b hb0
  set A := (Nat.digits 3 (k * b)).length
  set B := (Nat.digits 3 b).length
  have hgt : 3 ^ (m + B) < 3 ^ A := by
    rw [pow_add]
    calc 3 ^ m * 3 ^ B ≤ 3 ^ m * (3 * b) := Nat.mul_le_mul_left _ lb
      _ = (3 * 3 ^ m) * b := by ring
      _ < (2 * k) * b := Nat.mul_lt_mul_of_pos_right h1 hb0
      _ = 2 * (k * b) := by ring
      _ < 3 ^ A := ua
  have hlt : 3 ^ A < 3 ^ (m + B + 1) := by
    rw [pow_succ, pow_add]
    calc 3 ^ A ≤ 3 * (k * b) := la
      _ < 3 * ((2 * 3 ^ m) * b) := by
          apply Nat.mul_lt_mul_of_pos_left _ (by norm_num)
          exact Nat.mul_lt_mul_of_pos_right h2 hb0
      _ = 3 ^ m * (2 * b) * 3 := by ring
      _ < 3 ^ m * 3 ^ B * 3 := by
          apply Nat.mul_lt_mul_of_pos_right _ (by norm_num)
          exact Nat.mul_lt_mul_of_pos_left ub (by positivity)
  have e1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hgt
  have e2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hlt
  omega

/-- k ≡ 2 (mod 3) is never a quotient: strip common factors of 3 from b. -/
theorem not_quotient_of_mod3 (k : ℕ) (hk : k % 3 = 2) : ¬ IsQuot k := by
  rintro ⟨a, b, ha, hb, hb0, rfl⟩
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    have hdb : Nat.digits 3 b = b % 3 :: Nat.digits 3 (b / 3) := Nat.digits_def' (by norm_num) hb0
    have hdkb : Nat.digits 3 (k * b) = (k * b) % 3 :: Nat.digits 3 (k * b / 3) :=
      Nat.digits_def' (by norm_num) (Nat.mul_pos (by omega) hb0)
    have h0 : b % 3 ≤ 1 := hb _ (by rw [hdb]; exact List.mem_cons_self ..)
    have h0' : (k * b) % 3 ≤ 1 := ha _ (by rw [hdkb]; exact List.mem_cons_self ..)
    rcases (show b % 3 = 0 ∨ b % 3 = 1 by omega) with h | h
    · obtain ⟨c, rfl⟩ : ∃ c, b = 3 * c := ⟨b / 3, by omega⟩
      have hc0 : 0 < c := by omega
      have hcb : (3 * c) / 3 = c := by omega
      have hkc : (k * (3 * c)) / 3 = k * c := by rw [show k * (3 * c) = 3 * (k * c) by ring]; omega
      refine ih c (by omega) ?_ hc0 ?_
      · intro d hd; exact hb d (by rw [hdb, hcb]; exact List.mem_cons_of_mem _ hd)
      · intro d hd; exact ha d (by rw [hdkb, hkc]; exact List.mem_cons_of_mem _ hd)
    · have : (k * b) % 3 = 2 := by rw [Nat.mul_mod, hk, h]
      omega
