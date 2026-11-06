/-
OEIS A182372, step 3 of the README argument: the q-identity
  Σ_{l=0}^{b} x^{l(l+c)} [b choose l]_x (x^{c+l+1}; x)_{b-l} = 1     (b, c ≥ 0),
i.e. Σ_l x^{l(l+c)} [b,l]_x / (x;x)_{c+l} = 1/(x;x)_{b+c} after dividing by (x;x)_{b+c}.

Definitions (in Polynomial ℤ).
* `gauss b l`: Gaussian binomial [b choose l]_X by the q-Pascal rule
  [b+1, l+1] = [b, l+1] + X^(b-l) [b, l], [b, 0] = 1, [0, l+1] = 0.
* `poch a k = Π_{j<k} (1 - X^(a+j))`.

Main theorems.
* `qidentity b c : Σ_{l ≤ b} X^(l(l+c)) * gauss b l * poch (c+l+1) (b-l) = 1`.
* `subset_sum b l : Σ_{L ⊆ {0..b-1}, |L| = l} X^(Σ L) = X^(C(l,2)) * gauss b l` (used in step 2).

Not checked in this file: the other steps of the README (generating functions of the run shapes,
the bijection with two-sort partitions) and the link to the
OEIS definition of A182372.
-/
import Mathlib

open Polynomial Finset

namespace A182372

noncomputable def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | b + 1, l + 1 => gauss b (l + 1) + X ^ (b - l) * gauss b l

noncomputable def poch (a k : ℕ) : ℤ[X] := ∏ j ∈ range k, (1 - X ^ (a + j))

theorem gauss_zero_left (l : ℕ) : gauss 0 (l + 1) = 0 := rfl

theorem gauss_zero_right (b : ℕ) : gauss b 0 = 1 := by cases b <;> rfl

theorem gauss_succ (b l : ℕ) : gauss (b + 1) (l + 1) = gauss b (l + 1) + X ^ (b - l) * gauss b l := rfl

theorem gauss_gt : ∀ b l, b < l → gauss b l = 0
  | 0, l + 1, _ => rfl
  | b + 1, l + 1, h => by
    rw [gauss_succ, gauss_gt b (l + 1) (by omega), gauss_gt b l (by omega)]; simp
  | _, 0, h => absurd h (by omega)

theorem poch_succ (a k : ℕ) : poch a (k + 1) = poch a k * (1 - X ^ (a + k)) := by
  unfold poch; rw [prod_range_succ]

theorem qidentity : ∀ b c : ℕ,
    ∑ l ∈ range (b + 1), X ^ (l * (l + c)) * gauss b l * poch (c + l + 1) (b - l) = (1 : ℤ[X])
  | 0, c => by simp [gauss, poch]
  | b + 1, c => by
    have ih0 := qidentity b c
    have ih1 := qidentity b (c + 1)
    rw [sum_range_succ']
    -- part A: terms with gauss b (l+1), together with the l = 0 term
    have hA : ∑ l ∈ range (b + 1), X ^ ((l + 1) * (l + 1 + c)) * gauss b (l + 1) *
          poch (c + (l + 1) + 1) (b + 1 - (l + 1))
        + X ^ (0 * (0 + c)) * gauss (b + 1) 0 * poch (c + 0 + 1) (b + 1 - 0)
        = (1 - X ^ (b + c + 1)) := by
      have e := (sum_range_succ' (fun l => X ^ (l * (l + c)) * gauss b l *
        poch (c + l + 1) (b + 1 - l)) (b + 1)).symm
      have hg0 : gauss (b + 1) 0 = gauss b 0 := by rw [gauss_zero_right, gauss_zero_right]
      rw [hg0, e, sum_range_succ, gauss_gt b (b + 1) (by omega), mul_zero, zero_mul, add_zero]
      rw [show (1 : ℤ[X]) - X ^ (b + c + 1) = (∑ l ∈ range (b + 1), X ^ (l * (l + c)) * gauss b l *
          poch (c + l + 1) (b - l)) * (1 - X ^ (b + c + 1)) by rw [ih0, one_mul], sum_mul]
      refine sum_congr rfl (fun l hl => ?_)
      simp only [mem_range] at hl
      rw [show b + 1 - l = (b - l) + 1 by omega, poch_succ,
        show c + l + 1 + (b - l) = b + c + 1 by omega]
      ring
    have hB : ∑ l ∈ range (b + 1), X ^ ((l + 1) * (l + 1 + c)) * (X ^ (b - l) * gauss b l) *
          poch (c + (l + 1) + 1) (b + 1 - (l + 1)) = X ^ (b + c + 1) := by
      rw [← mul_one (X ^ (b + c + 1)), ← ih1, mul_sum]
      refine sum_congr rfl (fun l hl => ?_)
      simp only [mem_range] at hl
      rw [show b + 1 - (l + 1) = b - l by omega, show c + (l + 1) + 1 = c + 1 + l + 1 by omega]
      have hexp : (l + 1) * (l + 1 + c) + (b - l) = (b + c + 1) + l * (l + (c + 1)) := by
        have : l ≤ b := by omega
        zify [this]; ring
      calc X ^ ((l + 1) * (l + 1 + c)) * (X ^ (b - l) * gauss b l) * poch (c + 1 + l + 1) (b - l)
          = X ^ ((l + 1) * (l + 1 + c) + (b - l)) * gauss b l * poch (c + 1 + l + 1) (b - l) := by
            rw [pow_add]; ring
        _ = _ := by rw [hexp, pow_add]; ring
    have hsplit : ∑ l ∈ range (b + 1), X ^ ((l + 1) * (l + 1 + c)) * gauss (b + 1) (l + 1) *
          poch (c + (l + 1) + 1) (b + 1 - (l + 1))
        = ∑ l ∈ range (b + 1), X ^ ((l + 1) * (l + 1 + c)) * gauss b (l + 1) *
            poch (c + (l + 1) + 1) (b + 1 - (l + 1))
          + ∑ l ∈ range (b + 1), X ^ ((l + 1) * (l + 1 + c)) * (X ^ (b - l) * gauss b l) *
            poch (c + (l + 1) + 1) (b + 1 - (l + 1)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl (fun l _ => ?_)
      rw [gauss_succ]; ring
    rw [hsplit]
    linear_combination hA + hB


/-- Gaussian-binomial subset sum (step 2): Σ over l-subsets L of {0,...,b-1} of X^(Σ L)
equals X^(C(l,2)) [b choose l]_X. -/
theorem subset_sum : ∀ b l : ℕ,
    ∑ L ∈ (range b).powersetCard l, (X : ℤ[X]) ^ (∑ t ∈ L, t) = X ^ (l.choose 2) * gauss b l
  | b, 0 => by simp [gauss_zero_right]
  | 0, l + 1 => by rw [powersetCard_eq_empty.2 (by simp)]; simp [gauss_zero_left]
  | b + 1, l + 1 => by
    rw [range_add_one, powersetCard_succ_insert (by simp), sum_union, sum_image, subset_sum b (l + 1)]
    · have h2 : ∑ x ∈ (range b).powersetCard l, (X : ℤ[X]) ^ (∑ t ∈ insert b x, t)
          = X ^ b * (X ^ (l.choose 2) * gauss b l) := by
        rw [← subset_sum b l, mul_sum]
        refine sum_congr rfl (fun L hL => ?_)
        have hb : b ∉ L := by
          intro h; have := (mem_powersetCard.1 hL).1 h; simp at this
        rw [sum_insert hb, pow_add]
      rw [h2, gauss_succ]
      by_cases hl : l ≤ b
      · have hc : (l + 1).choose 2 + (b - l) = l.choose 2 + b := by
          have hc1 : (l + 1).choose 2 = l + l.choose 2 := by
            simpa [Nat.choose_one_right] using Nat.choose_succ_succ' l 1
          omega
        have : (X : ℤ[X]) ^ ((l + 1).choose 2) * X ^ (b - l) = X ^ (l.choose 2) * X ^ b := by
          rw [← pow_add, ← pow_add, hc]
        linear_combination (-(gauss b l)) * this
      · rw [gauss_gt b l (by omega)]; ring
    · intro L1 h1 L2 h2 he
      have hb1 : b ∉ L1 := by intro h; have := (mem_powersetCard.1 h1).1 h; simp at this
      have hb2 : b ∉ L2 := by intro h; have := (mem_powersetCard.1 h2).1 h; simp at this
      have := congrArg (fun L => L.erase b) he
      simpa [erase_insert hb1, erase_insert hb2] using this
    · rw [disjoint_left]
      intro L h1 h2
      obtain ⟨L', _, rfl⟩ := mem_image.1 h2
      have := (mem_powersetCard.1 h1).1 (mem_insert_self b L')
      simp at this
