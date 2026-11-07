import Mathlib

/-!
# OEIS A177960: the m-nomial conjecture holds

A177960 = numbers A001317(t), t not of the form c*(2^k - 1) with c >= 0, k >= 2.
Row n of the m-nomial triangle is the coefficient list of (1 + x + ... + x^(m-1))^n; reduced mod 2 and read
as binary digits (coefficient of x^i = bit i) it gives a number `rowNum m n`. A001317(t) = `rowNum 2 t`.
Conjecture (entry text): A177960 lists the terms of A001317 that are not row numbers for any m >= 3.

Checked here (`A177960_conjecture`): x ∈ A177960 ↔ x = A001317(t) for some t and x ≠ rowNum m n for all
m >= 3, n. `rowNum_eq` shows `rowNum` is the OEIS reading (sum of (coeff i mod 2) * 2^i over ℕ coefficients).
Not checked: nothing beyond reading the OEIS definitions as `rowNum` and `A177960set`.
-/

open Polynomial Finset

/-- 1 + x + ... + x^(m-1) over GF(2). -/
noncomputable def G (m : ℕ) : (ZMod 2)[X] := ∑ j ∈ range m, X ^ j

/-- Binary number with bit i = coefficient i (GF(2) polynomial). -/
noncomputable def num (f : (ZMod 2)[X]) : ℕ := ∑ i ∈ f.support, 2 ^ i

/-- The OEIS reading: m-nomial row n over ℕ, each coefficient reduced mod 2, bits to a number. -/
noncomputable def rowNum (m n : ℕ) : ℕ :=
  let f : ℕ[X] := (∑ j ∈ range m, (X : ℕ[X]) ^ j) ^ n
  ∑ i ∈ range (f.natDegree + 1), (f.coeff i % 2) * 2 ^ i

/-- A177960 as a set of values. -/
def A177960set (x : ℕ) : Prop :=
  ∃ t, x = rowNum 2 t ∧ ∀ c k, 2 ≤ k → t ≠ c * (2 ^ k - 1)

theorem rowNum_eq (m n : ℕ) : rowNum m n = num (G m ^ n) := by
  set f : ℕ[X] := (∑ j ∈ range m, (X : ℕ[X]) ^ j) ^ n with hf
  have hmap : G m ^ n = f.map (Nat.castRingHom (ZMod 2)) := by
    simp [hf, G, Polynomial.map_pow, Polynomial.map_sum]
  rw [hmap]
  unfold rowNum num
  rw [← hf]
  have hsub : (f.map (Nat.castRingHom (ZMod 2))).support ⊆ range (f.natDegree + 1) := by
    intro i hi
    rw [mem_support_iff, coeff_map] at hi
    rw [mem_range, Nat.lt_succ_iff]
    by_contra h
    exact hi (by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp)
  rw [← sum_subset hsub]
  · apply sum_congr rfl
    intro i hi
    rw [mem_support_iff, coeff_map] at hi
    simp only [Nat.coe_castRingHom] at hi
    have : f.coeff i % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (f.coeff i) with h | h
      · exact absurd ((ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h)) hi
      · exact h
    rw [this, one_mul]
  · intro i _ hi
    rw [mem_support_iff, coeff_map, not_not] at hi
    simp only [Nat.coe_castRingHom] at hi
    have := (ZMod.natCast_eq_zero_iff _ _).mp hi
    rw [Nat.mod_eq_zero_of_dvd this, zero_mul]

theorem coeff_zmod2 (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  revert a; decide

theorem num_injective : Function.Injective num := by
  intro f g h
  have hs : f.support = g.support := Finset.geomSum_injective le_rfl h
  ext i
  by_cases hi : i ∈ f.support
  · have hg : i ∈ g.support := hs ▸ hi
    rw [mem_support_iff] at hi hg
    rw [coeff_zmod2 _ hi, coeff_zmod2 _ hg]
  · have hg : i ∉ g.support := hs ▸ hi
    rw [notMem_support_iff] at hi hg
    rw [hi, hg]

local notation "P" => (X + 1 : (ZMod 2)[X])

theorem G_mul (m : ℕ) : G m * P = X ^ m + 1 := by
  have h := geom_sum_mul (X : (ZMod 2)[X]) m
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h
  exact h

theorem P_ne_zero : P ≠ 0 := X_add_C_ne_zero 1

theorem natDegree_X_pow_add_one (r : ℕ) : (X ^ r + 1 : (ZMod 2)[X]).natDegree = r := by
  have := natDegree_X_pow_add_C (R := ZMod 2) (n := r) (r := 1)
  rwa [C_1] at this

theorem P_not_unit : ¬ IsUnit P := by
  intro h
  have := natDegree_eq_zero_of_isUnit h
  rw [show (X + 1 : (ZMod 2)[X]) = X + C 1 by simp, natDegree_X_add_C] at this
  exact one_ne_zero this

/-- G(2^k * r) = G(r)^(2^k) * P^(2^k - 1). -/
theorem G_factor (k r : ℕ) : G (2 ^ k * r) = G r ^ (2 ^ k) * P ^ (2 ^ k - 1) := by
  apply mul_right_cancel₀ P_ne_zero
  rw [G_mul, mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), ← mul_pow, G_mul,
    add_pow_char_pow, one_pow, ← pow_mul, mul_comm r]

theorem G_one : G 1 = 1 := by simp [G]

theorem G_two : G 2 = P := by simp [G, Finset.sum_range_succ, add_comm]

theorem eval_G_odd (r : ℕ) (hr : Odd r) : (G r).eval 1 = 1 := by
  obtain ⟨s, rfl⟩ := hr
  simp only [G, eval_finsetSum, eval_pow, eval_X, one_pow, sum_const, card_range, nsmul_eq_mul,
    mul_one]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide]
  simp

/-- Key lemma: an m-nomial row (m >= 3) equal to a Pascal row mod 2 forces t = c*(2^k - 1), k >= 2. -/
theorem key (m n t : ℕ) (hm : 3 ≤ m) (h : G m ^ n = P ^ t) :
    ∃ c k, 2 ≤ k ∧ t = c * (2 ^ k - 1) := by
  obtain ⟨k, r, hr, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) (by omega)
  rw [G_factor, mul_pow, ← pow_mul, ← pow_mul] at h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [mul_zero, pow_zero, mul_one] at h
    rcases Nat.eq_zero_or_pos t with ht | ht
    · exact ⟨0, 2, le_rfl, by simp [ht]⟩
    · exact absurd (isUnit_pow_iff (by omega) |>.mp (h ▸ isUnit_one)) P_not_unit
  · -- compare powers of P
    rcases le_or_gt ((2 ^ k - 1) * n) t with hle | hlt
    · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
      rw [he, pow_add, mul_comm (G r ^ _)] at h
      have h2 := mul_left_cancel₀ (pow_ne_zero _ P_ne_zero) h
      have he0 : e = 0 := by
        by_contra hne
        have := congrArg (eval 1) h2
        rw [eval_pow, eval_G_odd r hr, one_pow, eval_pow] at this
        rw [eval_add, eval_X, eval_one, show (1 + 1 : ZMod 2) = 0 by decide, zero_pow hne] at this
        exact one_ne_zero this
      subst he0
      rw [pow_zero] at h2
      have hu : IsUnit (G r) :=
        (isUnit_pow_iff (by positivity)).mp (h2 ▸ isUnit_one)
      have hdeg := natDegree_eq_zero_of_isUnit hu
      have hr1 : r = 1 := by
        by_contra hne
        have h3 := congrArg natDegree (G_mul r)
        rw [natDegree_mul (hu.ne_zero) P_ne_zero, hdeg,
          natDegree_X_pow_add_one r, show (X + 1 : (ZMod 2)[X]) = X + C 1 by simp,
          natDegree_X_add_C] at h3
        omega
      subst hr1
      refine ⟨n, k, ?_, by rw [he]; ring⟩
      by_contra hk
      interval_cases k <;> omega
    · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt hlt
      have h' : P ^ t * (P ^ (e + 1) * G r ^ (2 ^ k * n)) = P ^ t * 1 := by
        rw [mul_one, ← mul_assoc, ← pow_add, ← add_assoc, ← he, mul_comm, h]
      have h2 := mul_left_cancel₀ (pow_ne_zero _ P_ne_zero) h'
      have hu : IsUnit (P ^ (e + 1)) := IsUnit.of_mul_eq_one _ h2
      exact (P_not_unit ((isUnit_pow_iff (by omega)).mp hu)).elim

/-- Conversely every c*(2^k - 1) with k >= 2 is a row of the 2^k-nomial triangle. -/
theorem G_two_pow (k c : ℕ) : G (2 ^ k) ^ c = P ^ (c * (2 ^ k - 1)) := by
  have := G_factor k 1
  rw [mul_one, G_one, one_pow, one_mul] at this
  rw [this, ← pow_mul, mul_comm]

/-- Main theorem: the conjecture in A177960. -/
theorem A177960_conjecture (x : ℕ) :
    A177960set x ↔ (∃ t, x = rowNum 2 t) ∧ ¬ ∃ m n, 3 ≤ m ∧ x = rowNum m n := by
  simp only [A177960set, rowNum_eq, G_two]
  constructor
  · rintro ⟨t, rfl, ht⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro ⟨m, n, hm, hx⟩
    obtain ⟨c, k, hk, htk⟩ := key m n t hm (num_injective hx).symm
    exact ht c k hk htk
  · rintro ⟨⟨t, rfl⟩, hno⟩
    refine ⟨t, rfl, ?_⟩
    intro c k hk htk
    apply hno
    refine ⟨2 ^ k, c, ?_, ?_⟩
    · calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    · rw [G_two_pow, htk]

