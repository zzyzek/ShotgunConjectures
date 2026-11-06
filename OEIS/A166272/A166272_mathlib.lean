import Mathlib

/-
OEIS A166272: numerator of A166100(A166101(n)) / A166102(n), where
A166100(m) = S(2m+1) = sum of the 1 <= i <= 2m+1 with Jacobi symbol J(i, 2m+1) = 1,
A166101 = the m with (2m+1) not dividing S(2m+1), A166102(n) = 2 A166101(n) + 1.
Conjecture (entry): A166272(n) = 3 A166100(A166101(n)) / A166102(n), i.e. the reduced
denominator of A166100(A166101(n)) / A166102(n) is always 3.

Main theorem.
* `A166272_conjecture`: for every m with (2m+1) not dividing A166100 m, the rational
  A166100 m / (2m+1) has denominator 3 and numerator 3 A166100 m / (2m+1).

Route: k | 3 S(k) for odd k (`dvd_three_S`, copied with its lemmas from
OEIS/A166103/A166103_mathlib.lean: multiplying by 4, J(4, k) = 1, permutes the residues
with J = 1). Write 3 S = k t; then 3 does not divide t (else k | S), so S/k = t/3 in lowest
terms.

Not checked in this file: agreement with the OEIS b-file (certificate/check.py).
-/

namespace OEIS_A166272

open Finset
/-- A166100 with k = 2n+1: sum of those 1 ≤ i ≤ k with Jacobi symbol J(i, k) = 1. -/
def S (k : ℕ) : ℕ := ∑ i ∈ Icc 1 k, if jacobiSym i k = 1 then i else 0

/-- The same sum over 0 ≤ i < k. -/
def S' (k : ℕ) : ℕ := ∑ i ∈ range k, if jacobiSym i k = 1 then i else 0

theorem S_eq (k : ℕ) (hk : 1 ≤ k) : S k = S' k + (if jacobiSym k k = 1 then k else 0) := by
  unfold S S'
  have h1 : Icc 1 k = (Ico 1 k) ∪ {k} := by
    ext x; simp; omega
  have h2 : range k = insert 0 (Ico 1 k) := by
    ext x; simp; omega
  rw [h1, h2, Finset.sum_union (by simp), Finset.sum_insert (by simp)]
  simp

theorem S_modeq (k : ℕ) (hk : 1 ≤ k) : (S k : ZMod k) = (S' k : ZMod k) := by
  rw [S_eq k hk]
  split_ifs <;> simp

theorem jac_mod (k a : ℕ) : jacobiSym ((a % k : ℕ) : ℤ) k = jacobiSym (a : ℤ) k := by
  rw [Int.natCast_mod, ← jacobiSym.mod_left]

theorem coprime_of_jac (k u : ℕ) (hk : 1 ≤ k) (hu : jacobiSym u k = 1) : Nat.Coprime u k := by
  have hne : NeZero k := ⟨by omega⟩
  have := (jacobiSym.eq_zero_iff_not_coprime (a := (u : ℤ)) (b := k)).not.mp (by rw [hu]; norm_num)
  rw [not_not, Int.gcd_natCast_natCast] at this
  exact this

/-- Multiplying by u with J(u, k) = 1 permutes {i < k : J(i, k) = 1} mod k. -/
theorem mul_invariant (k u : ℕ) (hk : 1 ≤ k) (hu : jacobiSym u k = 1) :
    ((u : ZMod k) * S' k : ZMod k) = S' k := by
  have hcop := coprime_of_jac k u hk hu
  have : NeZero k := ⟨by omega⟩
  set w := ZMod.unitOfCoprime u hcop
  set v : ℕ := ((w⁻¹ : (ZMod k)ˣ) : ZMod k).val
  have hvu : ((v : ℕ) : ZMod k) * (u : ZMod k) = 1 := by
    have hne : NeZero k := ⟨by omega⟩
    simp only [v, ZMod.natCast_val, ZMod.cast_id', id]
    have : ((w⁻¹ : (ZMod k)ˣ) : ZMod k) * (w : ZMod k) = 1 := by simp
    simp [w]
  have key : ∀ i ∈ range k, (((if jacobiSym ((u * i % k : ℕ) : ℤ) k = 1 then u * i % k else 0 : ℕ)) :
      ZMod k) = (u : ZMod k) * ((if jacobiSym (i : ℤ) k = 1 then i else 0 : ℕ) : ZMod k) := by
    intro i _
    rw [jac_mod, Nat.cast_mul, jacobiSym.mul_left, hu, one_mul]
    split_ifs
    · simp
    · simp
  unfold S'
  rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_congr rfl key, ← Nat.cast_sum, ← Nat.cast_sum]
  congr 1
  apply Finset.sum_nbij' (fun i => u * i % k) (fun i => v * i % k)
  · intro i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← ZMod.val_natCast_of_lt hi, ← ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < k))]
    congr 1
    push_cast [ZMod.natCast_mod]
    rw [← mul_assoc, hvu, one_mul, ZMod.natCast_zmod_val]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← ZMod.val_natCast_of_lt hi, ← ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < k))]
    congr 1
    push_cast [ZMod.natCast_mod]
    rw [← mul_assoc, mul_comm (u : ZMod k), hvu, one_mul, ZMod.natCast_zmod_val]
  · intro i _
    rfl

theorem S_three (k : ℕ) (hk : Odd k) : ((3 : ZMod k) * S k) = 0 := by
  have hk1 : 1 ≤ k := hk.pos
  have h4 := mul_invariant k 4 hk1 (by exact_mod_cast jacobiSym.at_four hk)
  rw [S_modeq k hk1]
  push_cast at h4
  linear_combination h4

/-- k ∣ 3 S(k) for every odd k. -/
theorem dvd_three_S (k : ℕ) (hk : Odd k) : k ∣ 3 * S k := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact S_three k hk


/-- A166100. -/
def A166100 (m : ℕ) : ℕ := S (2 * m + 1)

theorem A166272_conjecture (m : ℕ) (hm : ¬ (2 * m + 1) ∣ A166100 m) :
    ((A166100 m : ℚ) / (2 * m + 1 : ℕ)).den = 3 ∧
    ((A166100 m : ℚ) / (2 * m + 1 : ℕ)).num = (3 * A166100 m / (2 * m + 1) : ℕ) := by
  set k := 2 * m + 1 with hk
  have hodd : Odd k := ⟨m, by omega⟩
  obtain ⟨t, ht⟩ := dvd_three_S k hodd
  have ht3 : ¬ 3 ∣ t := by
    rintro ⟨s, rfl⟩
    apply hm
    exact ⟨s, by unfold A166100; rw [← hk]; linarith⟩
  have hkpos : 0 < k := by omega
  have hq : ((A166100 m : ℚ) / (k : ℕ)) = ((t : ℤ) : ℚ) / ((3 : ℤ) : ℚ) := by
    have h1 : (3 : ℚ) * (S k : ℚ) = (k : ℚ) * (t : ℚ) := by exact_mod_cast ht
    unfold A166100
    rw [← hk]
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
    field_simp
    push_cast
    linarith
  have hcop : Nat.Coprime ((t : ℤ).natAbs) ((3 : ℤ).natAbs) := by
    have h3 : ((3 : ℤ).natAbs) = 3 := rfl
    rw [Int.natAbs_natCast, h3]
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ht3))
  have hdiv : 3 * A166100 m / k = t := by
    unfold A166100; rw [← hk, ht]; exact Nat.mul_div_cancel_left t hkpos
  rw [hq, hdiv]
  refine ⟨?_, ?_⟩
  · have := Rat.den_div_eq_of_coprime (a := (t : ℤ)) (b := 3) (by norm_num) hcop
    exact_mod_cast this
  · exact Rat.num_div_eq_of_coprime (a := (t : ℤ)) (b := 3) (by norm_num) hcop
