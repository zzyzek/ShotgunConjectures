/-
OEIS A005430, Mathlib proof of R. J. Mathar's conjecture
  "the terms of the inverse binomial transform are 2*A132894(n)".

Definitions.
* `A005430 n` = n C(2n, n) (the entry's definition, offset 0).
* `A005430_invbin n` = Σ_{k=0..n} (-1)^(n-k) C(n,k) A005430(k) (inverse binomial transform).
* `A132894 n` = Σ_{k=0..n} k C(n,k) C(n-k, ⌊(n-k)/2⌋), the first formula of A132894.

Main theorem `A005430_conjecture`: A005430_invbin n = 2 A132894 n for every n.

Proof. With m = n - 1 and k C(n,k) = n C(m,k-1), C(2j+2,j+1) = 2 C(2j+1,j), both sides become
2n times the coefficient of x^m in (1+x)(1+x+x^2)^m:
* writing 1+x+x^2 = (1+x)^2 - x gives Σ_j (-1)^(m-j) C(m,j) C(2j+1,j) (`A005430_left`);
* writing 1+x+x^2 = x + (1+x^2) gives Σ_j C(m,j) C(j,⌊j/2⌋) (`A005430_right`).
`A005430_data`: the first terms of both sides (0, 2, 8, 30, 104, ...) and A132894 against the entry.

Not checked in Lean: that A132894's combinatorial definition (number of H steps in all length-n
left factors of Motzkin paths) equals the formula used here. That is the standard count: choose the
k positions of the H steps (C(n,k) ways) and a left factor of a Dyck path on the other n-k steps
(C(n-k, ⌊(n-k)/2⌋) ways); certificate/check.py confirms it by enumeration for n ≤ 12.
-/
import Mathlib

open Polynomial Finset

/-- A005430(n) = n C(2n, n). -/
def A005430 (n : ℕ) : ℕ := n * (2 * n).choose n

/-- Inverse binomial transform of A005430. -/
def A005430_invbin (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (n.choose k : ℤ) * (A005430 k : ℤ)

/-- A132894(n) = Σ_k k C(n,k) C(n-k, ⌊(n-k)/2⌋). -/
def A132894 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), k * n.choose k * (n - k).choose ((n - k) / 2)

theorem A005430_coeff_sq (j e : ℕ) :
    ((1 + X ^ 2 : ℤ[X]) ^ j).coeff e = if Even e then (j.choose (e / 2) : ℤ) else 0 := by
  rw [add_comm, add_pow, finsetSum_coeff]
  simp only [one_pow, mul_one, ← pow_mul, coeff_mul_natCast, coeff_X_pow]
  split_ifs with he
  · obtain ⟨t, rfl⟩ := he
    rw [show (t + t) / 2 = t by omega]
    by_cases ht : t ≤ j
    · rw [sum_eq_single t]
      · simp [show t + t = 2 * t by ring]
      · intro b _ hb
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
        simp
      · intro h
        exact absurd (mem_range.mpr (by omega)) h
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      refine sum_eq_zero fun i hi => ?_
      rw [mem_range] at hi
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      simp
  · refine sum_eq_zero fun i _ => ?_
    rw [ite_eq_right_iff.mpr (fun h => absurd ⟨i, by omega⟩ he)]
    simp

/-- Σ_j (-1)^(m-j) C(m,j) C(2j+1,j) = [x^m] (1+x)(1+x+x^2)^m. -/
theorem A005430_left (m : ℕ) :
    ((1 + X : ℤ[X]) * (1 + X + X ^ 2) ^ m).coeff m =
      ∑ j ∈ range (m + 1), (-1) ^ (m - j) * (m.choose j : ℤ) * ((2 * j + 1).choose j : ℤ) := by
  rw [show (1 + X + X ^ 2 : ℤ[X]) = (1 + X) ^ 2 + (-X) by ring, add_pow, mul_sum, finsetSum_coeff]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [show (1 + X : ℤ[X]) * (((1 + X) ^ 2) ^ j * (-X) ^ (m - j) * (m.choose j : ℤ[X])) =
      C ((-1) ^ (m - j) * (m.choose j : ℤ)) * ((X + 1) ^ (2 * j + 1) * X ^ (m - j)) by
    rw [← pow_mul, neg_pow, map_mul, map_pow, map_neg, map_one, map_natCast]; ring]
  rw [coeff_C_mul, coeff_mul_X_pow', ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
    show m - (m - j) = j by omega, coeff_X_add_one_pow]

/-- Σ_j C(m,j) C(j,⌊j/2⌋) = [x^m] (1+x)(1+x+x^2)^m. -/
theorem A005430_right (m : ℕ) :
    ((1 + X : ℤ[X]) * (1 + X + X ^ 2) ^ m).coeff m =
      ∑ j ∈ range (m + 1), (m.choose j : ℤ) * (j.choose (j / 2) : ℤ) := by
  rw [show (1 + X + X ^ 2 : ℤ[X]) = (1 + X ^ 2) + X by ring, add_pow, mul_sum, finsetSum_coeff]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [show (1 + X : ℤ[X]) * ((1 + X ^ 2) ^ j * X ^ (m - j) * (m.choose j : ℤ[X])) =
      C (m.choose j : ℤ) * ((1 + X ^ 2) ^ j * X ^ (m - j)) +
        C (m.choose j : ℤ) * ((1 + X ^ 2) ^ j * X ^ (m - j + 1)) by
    rw [map_natCast]; ring]
  rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow', coeff_mul_X_pow',
    ite_eq_left_iff.mpr (fun h => absurd (by omega) h), show m - (m - j) = j by omega,
    A005430_coeff_sq, A005430_coeff_sq]
  rcases Nat.even_or_odd j with he | ho
  · have hne : m - j + 1 ≤ m → ¬ Even (m - (m - j + 1)) := by
      intro h1 h2
      obtain ⟨t, ht⟩ := he
      obtain ⟨u, hu⟩ := h2
      omega
    rw [ite_eq_left_iff.mpr (fun h => absurd he h)]
    split_ifs with h1 h2
    · exact absurd h2 (hne h1)
    · ring
    · ring
  · obtain ⟨t, rfl⟩ := ho
    have hodd : ¬ Even (2 * t + 1) := Nat.not_even_iff_odd.mpr ⟨t, rfl⟩
    rw [ite_eq_right_iff.mpr (fun h => absurd h hodd), ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
      show m - (m - (2 * t + 1) + 1) = 2 * t by omega,
      ite_eq_left_iff.mpr (fun h => absurd ⟨t, by ring⟩ h),
      show 2 * t / 2 = t by omega, show (2 * t + 1) / 2 = t by omega]
    ring

theorem A005430_choose_two (j : ℕ) : (2 * (j + 1)).choose (j + 1) = 2 * (2 * j + 1).choose j := by
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.choose_succ_succ,
    Nat.choose_symm_of_eq_add (show 2 * j + 1 = (j + 1) + j by ring)]
  ring

theorem A005430_conjecture (n : ℕ) : A005430_invbin n = 2 * (A132894 n : ℤ) := by
  rcases n with _ | m
  · simp [A005430_invbin, A132894, A005430]
  have hL : A005430_invbin (m + 1) =
      2 * (m + 1 : ℤ) * ((1 + X : ℤ[X]) * (1 + X + X ^ 2) ^ m).coeff m := by
    rw [A005430_left, A005430_invbin, sum_range_succ']
    simp only [A005430, zero_mul, Nat.cast_zero, mul_zero, add_zero]
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have h1 : ((m + 1).choose (j + 1) : ℤ) * (j + 1 : ℤ) = (m + 1 : ℤ) * (m.choose j : ℤ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m j).symm
    rw [show m + 1 - (j + 1) = m - j by omega, A005430_choose_two]
    push_cast
    linear_combination (-1) ^ (m - j) * 2 * ((2 * j + 1).choose j : ℤ) * h1
  have hR : (A132894 (m + 1) : ℤ) =
      (m + 1 : ℤ) * ((1 + X : ℤ[X]) * (1 + X + X ^ 2) ^ m).coeff m := by
    rw [A005430_right, A132894, sum_range_succ',
      ← sum_range_reflect (fun j => (m.choose j : ℤ) * (j.choose (j / 2) : ℤ)) (m + 1), mul_sum]
    push_cast
    simp only [zero_mul, add_zero]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have h1 : ((m + 1).choose (j + 1) : ℤ) * (j + 1 : ℤ) = (m + 1 : ℤ) * (m.choose j : ℤ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m j).symm
    rw [Nat.choose_symm (by omega : j ≤ m)]
    linear_combination ((m - j).choose ((m - j) / 2) : ℤ) * h1
  rw [hL, hR]
  ring

theorem A005430_data :
    (List.range 12).map A005430_invbin = [0, 2, 8, 30, 104, 350, 1152, 3738, 12000, 38214, 120920, 380666] ∧
    (List.range 14).map A132894 = [0, 1, 4, 15, 52, 175, 576, 1869, 6000, 19107, 60460, 190333, 596652, 1863745] ∧
    (List.range 13).map A005430 = [0, 2, 12, 60, 280, 1260, 5544, 24024, 102960, 437580, 1847560, 7759752, 32449872] := by
  decide
