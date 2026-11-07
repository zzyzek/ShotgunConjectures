/-
OEIS A173643 (Mathlib): positive numbers of the form 2^m - 2^l - 3*2^k (m > l > k >= 0, as in A172233)
divisible by 9, divided by 9. Conjecture in the entry: the odd part of every term is
((8^M - (-1)^M - 3)/6 * 4^K - 1)/3 for some K, M > 0.

Checked here: the conjecture is false. 3 is a term (2^5 - 2^1 - 3*2^0 = 27 = 9*3, it is a(3)), its odd part is
3, and no K, M > 0 give 3 (`A173643_conjecture_false`).
Also checked: `A173643_corrected`, the odd part of every term has the form with M > 0 and K >= 0 (the failures
of K > 0 are K = 0 with M even: 3, 227, 14563, ...).
-/
import Mathlib

/-- Membership in A173643. -/
def A173643_mem (a : ℕ) : Prop :=
  ∃ m l k : ℕ, l < m ∧ k < l ∧ 2 ^ l + 3 * 2 ^ k < 2 ^ m ∧ 9 ∣ 2 ^ m - 2 ^ l - 3 * 2 ^ k ∧
    a = (2 ^ m - 2 ^ l - 3 * 2 ^ k) / 9

/-- Odd part. -/
def A173643_oddPart (a : ℕ) : ℕ := a / 2 ^ padicValNat 2 a

/-- The form in the conjecture, computed in ℚ. -/
def A173643_form (M K : ℕ) : ℚ := (((8 : ℚ) ^ M - (-1) ^ M - 3) / 6 * 4 ^ K - 1) / 3

theorem A173643_three_mem : A173643_mem 3 := ⟨5, 1, 0, by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num⟩

theorem A173643_oddPart_three : A173643_oddPart 3 = 3 := by
  unfold A173643_oddPart
  rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem A173643_form_ne_three (M K : ℕ) (hM : 0 < M) (hK : 0 < K) : A173643_form M K ≠ 3 := by
  intro h
  unfold A173643_form at h
  have hP : (4 : ℚ) ≤ 4 ^ K := by
    calc (4 : ℚ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK
  rcases Nat.even_or_odd M with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [Even.neg_one_pow ⟨j, rfl⟩] at h
    have hj : 1 ≤ j := by omega
    have hQ : (64 : ℚ) ≤ 8 ^ (j + j) := by
      calc (64 : ℚ) = 8 ^ 2 := by norm_num
        _ ≤ 8 ^ (j + j) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  · rw [Odd.neg_one_pow ⟨j, rfl⟩] at h
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rcases Nat.lt_or_ge K 2 with hK2 | hK2
      · obtain rfl : K = 1 := by omega
        norm_num at h
      · have hP' : (16 : ℚ) ≤ 4 ^ K := by
          calc (16 : ℚ) = 4 ^ 2 := by norm_num
            _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK2
        norm_num at h
        nlinarith
    · have hQ : (512 : ℚ) ≤ 8 ^ (2 * j + 1) := by
        calc (512 : ℚ) = 8 ^ 3 := by norm_num
          _ ≤ 8 ^ (2 * j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith

/-- Main theorem: the conjecture (every term's odd part has the form with K, M > 0) is false. -/
theorem A173643_conjecture_false :
    ¬ (∀ a, A173643_mem a → ∃ M K : ℕ, 0 < M ∧ 0 < K ∧
      (A173643_oddPart a : ℚ) = A173643_form M K) := by
  intro h
  obtain ⟨M, K, hM, hK, hf⟩ := h 3 A173643_three_mem
  rw [A173643_oddPart_three] at hf
  exact A173643_form_ne_three M K hM hK (by rw [← hf]; norm_num)

/-! Corrected statement: the odd part always has the form with M > 0 and K ≥ 0. -/

theorem A173643_pow_mod9 (n : ℕ) : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem A173643_cases (B D : ℕ) (h : (2 ^ B * 2 ^ D) % 9 = (2 ^ B + 3) % 9) :
    (D % 6 = 2 ∧ B % 2 = 0) ∨ (D % 6 = 4 ∧ B % 2 = 1) := by
  rw [Nat.mul_mod, A173643_pow_mod9 B, A173643_pow_mod9 D, Nat.add_mod, A173643_pow_mod9 B] at h
  have hB : B % 2 = (B % 6) % 2 := by omega
  rw [hB]
  have h6 : B % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have h6' : D % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize B % 6 = r at *
  generalize D % 6 = s at *
  interval_cases r <;> interval_cases s <;> simp_all

theorem A173643_odd_part_form (B D : ℕ) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (h9 : (2 ^ B * 2 ^ D) % 9 = (2 ^ B + 3) % 9) :
    ∃ M K : ℕ, 0 < M ∧ ((2 : ℚ) ^ B * 2 ^ D - 2 ^ B - 3) / 9 = A173643_form M K := by
  unfold A173643_form
  rcases A173643_cases B D h9 with ⟨hs, hr⟩ | ⟨hs, hr⟩
  · obtain ⟨d, rfl⟩ : ∃ d, D = 6 * d + 2 := ⟨D / 6, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, B = 2 * K := ⟨B / 2, by omega⟩
    refine ⟨2 * d + 1, K, by omega, ?_⟩
    rw [Odd.neg_one_pow ⟨d, rfl⟩]
    have e1 : (8 : ℚ) ^ (2 * d + 1) = 8 * 64 ^ d := by rw [pow_succ, pow_mul]; norm_num; ring
    have e2 : (2 : ℚ) ^ (6 * d + 2) = 4 * 64 ^ d := by rw [pow_add, pow_mul]; norm_num; ring
    have e3 : (2 : ℚ) ^ (2 * K) = 4 ^ K := by rw [pow_mul]; norm_num
    rw [e1, e2, e3]
    ring
  · obtain ⟨d, rfl⟩ : ∃ d, D = 6 * d + 4 := ⟨D / 6, by omega⟩
    obtain ⟨K, rfl⟩ : ∃ K, B = 2 * K + 1 := ⟨B / 2, by omega⟩
    refine ⟨2 * d + 2, K, by omega, ?_⟩
    rw [Even.neg_one_pow ⟨d + 1, by ring⟩]
    have e1 : (8 : ℚ) ^ (2 * d + 2) = 64 * 64 ^ d := by rw [pow_add, pow_mul]; norm_num; ring
    have e2 : (2 : ℚ) ^ (6 * d + 4) = 16 * 64 ^ d := by rw [pow_add, pow_mul]; norm_num; ring
    have e3 : (2 : ℚ) ^ (2 * K + 1) = 2 * 4 ^ K := by rw [pow_succ, pow_mul]; norm_num; ring
    rw [e1, e2, e3]
    ring

theorem A173643_oddPart_mul (k w : ℕ) (hw : ¬ 2 ∣ w) : A173643_oddPart (2 ^ k * w) = w := by
  unfold A173643_oddPart
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero 2)
  rw [padicValNat.mul (by positivity) hw0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hw,
    Nat.add_zero, Nat.mul_div_cancel_left _ (by positivity)]

/-- Corrected theorem: every term's odd part is ((8^M - (-1)^M - 3)/6 * 4^K - 1)/3 with M > 0, K ≥ 0. -/
theorem A173643_corrected (a : ℕ) (ha : A173643_mem a) :
    ∃ M K : ℕ, 0 < M ∧ (A173643_oddPart a : ℚ) = A173643_form M K := by
  obtain ⟨m, l, k, hml, hlk, hpos, h9, rfl⟩ := ha
  obtain ⟨B, rfl⟩ : ∃ B, l = k + B := ⟨l - k, by omega⟩
  obtain ⟨D, rfl⟩ : ∃ D, m = k + B + D := ⟨m - (k + B), by omega⟩
  have hB : 1 ≤ B := by omega
  have hD : 1 ≤ D := by omega
  have e1 : 2 ^ (k + B + D) = 2 ^ k * (2 ^ B * 2 ^ D) := by rw [pow_add, pow_add]; ring
  have e2 : 2 ^ (k + B) = 2 ^ k * 2 ^ B := pow_add _ _ _
  rw [e1, e2] at hpos h9 ⊢
  have hP : 0 < 2 ^ k := by positivity
  have hle : 2 ^ B + 3 ≤ 2 ^ B * 2 ^ D := by
    have : 2 ^ k * (2 ^ B + 3) < 2 ^ k * (2 ^ B * 2 ^ D) := by rw [mul_add]; linarith
    exact (Nat.lt_of_mul_lt_mul_left this).le
  have hmod : (2 ^ B * 2 ^ D) % 9 = (2 ^ B + 3) % 9 := by
    have hy : 2 ^ k * (2 ^ B * 2 ^ D) - 2 ^ k * 2 ^ B - 3 * 2 ^ k =
        2 ^ k * (2 ^ B * 2 ^ D - 2 ^ B - 3) := by
      rw [Nat.mul_sub, Nat.mul_sub, mul_comm 3 (2 ^ k)]
    rw [hy] at h9
    have h9' : 9 ∣ 2 ^ B * 2 ^ D - 2 ^ B - 3 :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right _ (by norm_num)) h9
    omega
  have hy : 2 ^ k * (2 ^ B * 2 ^ D) - 2 ^ k * 2 ^ B - 3 * 2 ^ k =
      2 ^ k * (2 ^ B * 2 ^ D - 2 ^ B - 3) := by
    rw [Nat.mul_sub, Nat.mul_sub, mul_comm 3 (2 ^ k)]
  rw [hy]
  have h9' : 9 ∣ 2 ^ B * 2 ^ D - 2 ^ B - 3 := by omega
  rw [Nat.mul_div_assoc _ h9']
  obtain ⟨c, hc⟩ := h9'
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  have hodd : ¬ 2 ∣ c := by
    intro h2
    have h2B : 2 ∣ 2 ^ B := dvd_pow_self 2 (by omega)
    have h2D : 2 ∣ 2 ^ B * 2 ^ D := Dvd.dvd.mul_right h2B _
    omega
  rw [A173643_oddPart_mul k c hodd]
  obtain ⟨M, K, hM, hf⟩ := A173643_odd_part_form B D hB hD hmod
  refine ⟨M, K, hM, ?_⟩
  rw [← hf]
  have hcast : ((2 ^ B * 2 ^ D - 2 ^ B - 3 : ℕ) : ℚ) = (2 : ℚ) ^ B * 2 ^ D - 2 ^ B - 3 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hc] at hcast
  push_cast at hcast
  linarith
