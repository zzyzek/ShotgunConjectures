import Mathlib

/-!
# Small general lemmas: descending factorials, squares in `ZMod p`

Main results.
* `descFactorial_mono` : `n.descFactorial k ≤ n.descFactorial l` for `k ≤ l ≤ n`.
* `two_ne_zero_zmod` : `(2 : ZMod p) ≠ 0` for a prime `p > 2`.
* `sum_squares_zero` : for a prime `p > 3`, the sum of the distinct squares in `ZMod p` is `0`.
* `exists_nonsq` : for a prime `p > 3` and nonzero `a, b, C` in `ZMod p`, some `a (b x² - C)` is
  a non-square (otherwise `s ↦ a (b s - C)` permutes the squares, and comparing sums gives
  `a C · #squares = 0`).

Used by OEIS A096123 (`descFactorial_mono`) and A176948 (`exists_nonsq`).
-/

namespace OpenProblemsLib.Misc

open Finset

/-- `k ↦ n (n-1) ... (n-k+1)` is monotone for `k ≤ n`. -/
theorem descFactorial_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ n) :
    n.descFactorial k ≤ n.descFactorial l := by
  induction l with
  | zero => simp_all
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le hkl with h | h
    · rw [h]
    · rw [Nat.descFactorial_succ]
      have h1 := ih (by omega) (by omega)
      have h2 : 1 ≤ n - l := by omega
      calc n.descFactorial k ≤ n.descFactorial l := h1
        _ ≤ (n - l) * n.descFactorial l := Nat.le_mul_of_pos_left _ h2

/-- `2 ≠ 0` in `ZMod p` for a prime `p > 2`. -/
theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

/-- The sum of the distinct squares in `ZMod p` is `0` for a prime `p > 3` (each nonzero
square is hit twice by `x ↦ x²`, and `∑ x² = 0`). -/
theorem sum_squares_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∑ s ∈ (univ : Finset (ZMod p)).image (fun x => x ^ 2), s = 0 := by
  have h2 := two_ne_zero_zmod p (by omega)
  have hsum : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have key : ∑ x : ZMod p, x ^ 2 =
      ∑ s ∈ (univ : Finset (ZMod p)).image (fun x => x ^ 2), (2 : ZMod p) * s := by
    rw [Finset.sum_comp (fun s : ZMod p => s) (fun x : ZMod p => x ^ 2)]
    apply sum_congr rfl
    intro s hs
    obtain ⟨y, -, rfl⟩ := mem_image.mp hs
    by_cases hy : y = 0
    · simp [hy]
    · have hne : y ≠ -y := by
        intro h
        have : (2 : ZMod p) * y = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · exact h2 h'
        · exact hy h'
      have hf : (univ.filter (fun x : ZMod p => x ^ 2 = y ^ 2)) = {y, -y} := by
        ext x; simp [sq_eq_sq_iff_eq_or_eq_neg]
      rw [hf, card_pair hne]
      simp [two_smul, two_mul]
  rw [hsum, ← mul_sum] at key
  exact (mul_eq_zero.mp key.symm).resolve_left h2

/-- For nonzero `a, b, C` some value `a (b x² - C)` is a non-square mod a prime `p > 3`. -/
theorem exists_nonsq (p : ℕ) [Fact p.Prime] (hp : 3 < p) (a b C : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hC : C ≠ 0) : ∃ x : ZMod p, ¬ IsSquare (a * (b * x ^ 2 - C)) := by
  by_contra hcon
  push Not at hcon
  set S := (univ : Finset (ZMod p)).image (fun x => x ^ 2) with hS
  have memS : ∀ t, t ∈ S ↔ IsSquare t := by
    intro t
    simp only [hS, mem_image, mem_univ, true_and, IsSquare, sq]
    constructor
    · rintro ⟨r, rfl⟩; exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩; exact ⟨r, rfl⟩
  set f : ZMod p → ZMod p := fun s => a * (b * s - C) with hf
  have hmap : ∀ s ∈ S, f s ∈ S := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.mp hs
    exact (memS _).mpr (hcon x)
  have hinj : Set.InjOn f S := by
    intro s _ t _ h
    have h' : a * b * (s - t) = 0 := by simp only [hf] at h; linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 (mul_ne_zero ha hb)
    · exact sub_eq_zero.mp h1
  have himg : S.image f = S :=
    eq_of_subset_of_card_le (image_subset_iff.mpr hmap) (card_image_of_injOn hinj).ge
  have hsum : ∑ s ∈ S, f s = ∑ s ∈ S, s := by
    calc ∑ s ∈ S, f s = ∑ s ∈ S.image f, s := (sum_image (f := fun s => s) hinj).symm
      _ = ∑ s ∈ S, s := by rw [himg]
  have h0 := sum_squares_zero p hp
  rw [← hS] at h0
  have e : ∑ s ∈ S, f s = a * b * ∑ s ∈ S, s - S.card • (a * C) := by
    calc ∑ s ∈ S, f s = ∑ s ∈ S, (a * b * s - a * C) :=
          sum_congr rfl (fun s _ => by simp only [hf]; ring)
      _ = a * b * ∑ s ∈ S, s - S.card • (a * C) := by rw [sum_sub_distrib, mul_sum, sum_const]
  rw [e, h0, nsmul_eq_mul] at hsum
  have hcardS : (S.card : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hpos : 0 < S.card := card_pos.mpr ⟨0, (memS 0).mpr ⟨0, by ring⟩⟩
    have hlt : S.card < p := by
      obtain ⟨r, hr⟩ := FiniteField.exists_nonsquare (F := ZMod p)
        (by rw [ZMod.ringChar_zmod_n]; omega)
      have hss : S ⊂ univ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨subset_univ _, fun h => hr ((memS r).mp (h ▸ mem_univ r))⟩
      have := card_lt_card hss
      rwa [card_univ, ZMod.card] at this
    exact absurd (Nat.le_of_dvd hpos h) (by omega)
  have : a * C * (S.card : ZMod p) = 0 := by linear_combination -hsum
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ha h2
    · exact hC h2
  · exact hcardS h1

end OpenProblemsLib.Misc
