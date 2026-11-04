/-
OEIS A197521, Mathlib proof.

Main theorem `A197521_main`: there is t0 such that
- t0 is the least t > 0 with sin(πt/6) = sin(πt/3)^2 (the A197383 constant), and
- 3 + t0 is the least x > 0 with cos(πx/2) = cos(πx/3)^2 (the A197521 constant).
This is the README result: the A197521 constant is 3 plus the A197383
constant. (Both least elements are stated with `IsLeast`.)

Proof: with x = t + 3, θ = πt/6, s = sin θ and g(s) = 4s^3 - 4s + 1, the
A197521 equation is (s + 1) g(s) = 0 and the A197383 equation is s g(s) = 0.
g has a root s1 ∈ (0, 1/2) (intermediate value theorem), g is decreasing on
[0, 1/2] and g ≥ 1 on [-1, 0]; t0 = (6/π) arcsin(s1). For x ∈ (0, 3 + t0)
one has θ ∈ (-π/2, arcsin s1), so s ∈ (-1, s1) and (s + 1) g(s) > 0; for
t ∈ (0, t0), s ∈ (0, s1) and s g(s) > 0.

Not checked: the numerical value 3.52133782... (not part of the claim).
-/
import Mathlib

open Real

/-- The cubic factor 4s^3 - 4s + 1. -/
def A197521_g (s : ℝ) : ℝ := 4 * s ^ 3 - 4 * s + 1

theorem A197521_eqF (x : ℝ) :
    cos (π * x / 2) = cos (π * x / 3) ^ 2 ↔
      (sin (π * (x - 3) / 6) + 1) * A197521_g (sin (π * (x - 3) / 6)) = 0 := by
  set θ := π * (x - 3) / 6 with hθ
  have h1 : cos (π * x / 2) = sin (3 * θ) := by
    rw [← cos_sub_pi_div_two, ← cos_add_two_pi (3 * θ - π / 2)]
    congr 1
    rw [hθ]
    ring
  have h2 : cos (π * x / 3) = -cos (2 * θ) := by
    rw [← cos_add_pi]
    congr 1
    rw [hθ]
    ring
  rw [h1, h2, sin_three_mul, neg_sq, cos_two_mul, cos_sq', A197521_g]
  constructor <;> intro h <;> linear_combination -h

theorem A197521_eqG (t : ℝ) :
    sin (π * t / 6) = sin (π * t / 3) ^ 2 ↔
      sin (π * t / 6) * A197521_g (sin (π * t / 6)) = 0 := by
  set θ := π * t / 6 with hθ
  have h1 : π * t / 3 = 2 * θ := by rw [hθ]; ring
  rw [h1, sin_two_mul, mul_pow, mul_pow, cos_sq', A197521_g]
  constructor <;> intro h <;> linear_combination h

theorem A197521_root : ∃ s1 : ℝ, 0 < s1 ∧ s1 < 1 / 2 ∧ A197521_g s1 = 0 ∧
    ∀ s, 0 ≤ s → s < s1 → 0 < A197521_g s := by
  have hcont : ContinuousOn A197521_g (Set.Icc 0 (1 / 2)) := by
    unfold A197521_g
    fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc (A197521_g (1 / 2)) (A197521_g 0) := by
    unfold A197521_g
    constructor <;> norm_num
  obtain ⟨s1, ⟨hs0, hs1⟩, hg⟩ := intermediate_value_Icc' (by norm_num) hcont h0
  have hne0 : s1 ≠ 0 := by
    rintro rfl
    unfold A197521_g at hg
    norm_num at hg
  have hne1 : s1 ≠ 1 / 2 := by
    rintro rfl
    unfold A197521_g at hg
    norm_num at hg
  refine ⟨s1, lt_of_le_of_ne hs0 (Ne.symm hne0), lt_of_le_of_ne hs1 hne1, hg, ?_⟩
  intro s hs hss
  have : A197521_g s - A197521_g s1 = 4 * (s - s1) * (s ^ 2 + s * s1 + s1 ^ 2 - 1) := by
    unfold A197521_g
    ring
  have hneg : s ^ 2 + s * s1 + s1 ^ 2 - 1 < 0 := by nlinarith
  have hpos : 0 < 4 * (s - s1) * (s ^ 2 + s * s1 + s1 ^ 2 - 1) := by
    have : s - s1 < 0 := by linarith
    nlinarith
  linarith

theorem A197521_main : ∃ t0 : ℝ,
    IsLeast {t : ℝ | 0 < t ∧ sin (π * t / 6) = sin (π * t / 3) ^ 2} t0 ∧
    IsLeast {x : ℝ | 0 < x ∧ cos (π * x / 2) = cos (π * x / 3) ^ 2} (3 + t0) := by
  obtain ⟨s1, hs0, hs1, hg, hdec⟩ := A197521_root
  set θ0 := arcsin s1 with hθ0
  have hθpos : 0 < θ0 := arcsin_pos.mpr hs0
  have hθlt : θ0 < π / 2 := arcsin_lt_pi_div_two.mpr (by linarith)
  have hsinθ : sin θ0 = s1 := sin_arcsin (by linarith) (by linarith)
  have hpi := pi_pos
  set t0 := 6 * θ0 / π with ht0
  have ht0pos : 0 < t0 := by positivity
  have hθt : π * t0 / 6 = θ0 := by rw [ht0]; field_simp
  -- Below θ0 (and above -π/2) the sine stays in (-1, s1).
  --
  have hsin_lt : ∀ θ, -(π / 2) ≤ θ → θ < θ0 → sin θ < s1 := by
    intro θ h1 h2
    rw [← hsinθ]
    exact strictMonoOn_sin ⟨h1, by linarith⟩ ⟨by linarith, hθlt.le⟩ h2
  have hgneg : ∀ s, -1 ≤ s → s ≤ 0 → 0 < A197521_g s := by
    intro s h1 h2
    unfold A197521_g
    have h3 : (0 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
    nlinarith [mul_nonneg (neg_nonneg.mpr h2) h3]
  refine ⟨t0, ⟨⟨ht0pos, ?_⟩, ?_⟩, ⟨⟨by linarith, ?_⟩, ?_⟩⟩
  · rw [A197521_eqG, hθt, hsinθ, hg, mul_zero]
  · rintro t ⟨htpos, ht⟩
    by_contra hlt
    push Not at hlt
    rw [A197521_eqG] at ht
    set θ := π * t / 6 with hθ
    have hθ1 : 0 < θ := by positivity
    have hθ2 : θ < θ0 := by
      rw [← hθt, hθ]
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt hpi) (by norm_num)
    have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ1 (by linarith)
    have hs' : sin θ < s1 := hsin_lt θ (by linarith) hθ2
    have := hdec (sin θ) hs.le hs'
    have : 0 < sin θ * A197521_g (sin θ) := mul_pos hs this
    linarith
  · rw [A197521_eqF, show 3 + t0 - 3 = t0 by ring, hθt, hsinθ, hg, mul_zero]
  · rintro x ⟨hxpos, hx⟩
    by_contra hlt
    push Not at hlt
    rw [A197521_eqF] at hx
    set θ := π * (x - 3) / 6 with hθ
    have hθ1 : -(π / 2) < θ := by
      rw [hθ]
      nlinarith
    have hθ2 : θ < θ0 := by
      rw [← hθt, hθ]
      have : x - 3 < t0 := by linarith
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left this hpi) (by norm_num)
    have hs1' : sin θ < s1 := hsin_lt θ hθ1.le hθ2
    have hsm1 : -1 < sin θ := by
      have hm : sin (-(π / 2)) = -1 := by rw [sin_neg, sin_pi_div_two]
      rw [← hm]
      exact strictMonoOn_sin ⟨le_refl _, by linarith⟩ ⟨hθ1.le, by linarith⟩ hθ1
    have hgpos : 0 < A197521_g (sin θ) := by
      rcases le_or_gt (sin θ) 0 with h | h
      · exact hgneg _ hsm1.le h
      · exact hdec _ h.le hs1'
    have : 0 < (sin θ + 1) * A197521_g (sin θ) := mul_pos (by linarith) hgpos
    linarith
