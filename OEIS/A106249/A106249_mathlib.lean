/-
OEIS A106249, Mathlib proof.

A106249: expansion of (1 - x + x^2 + x^3)/((1 + x)(1 + x^2)(1 - x)^2),
offset 0. Conjecture (M. Lagneau, 2012): number of roots of x^n + 1 in the
left half-plane, n > 0.

Reading (README): "left half-plane" is the open one, Re z < 0; the roots of
x^m + 1 are counted as the distinct complex z with z^m = -1
(`Polynomial.nthRootsFinset m (-1 : ℂ)`; they are simple). Literally the
statement is off by one (a(1) = 0, but x + 1 has the root -1); the result is
a(n) = number of roots of x^(n+1) + 1 with negative real part.

Main theorem `A106249_main`:
* for every n ≥ 0, the coefficient of x^n of the power series
  (1 - X + X^2 + X^3) · ((1 + X)(1 + X^2)(1 - X)^2)⁻¹ in ℚ⟦X⟧ equals
  #{z ∈ ℂ : z^(n+1) = -1, Re z < 0};
* the literal indexing fails at n = 1: the coefficient is 0 but z + 1 has
  the root z = -1 with negative real part.
This is the README result. Proof: the roots are exp(iπ(2j+1)/m), j < m; the
real part cos(π(2j+1)/m) is negative iff m < 2(2j+1) < 3m; this count is
2⌊m/4⌋ + (m mod 2), and the series has these coefficients (it times the
denominator 1 - X - X^4 + X^5 is the numerator). Nothing is outside Lean.
-/
import Mathlib

open Complex Real

/-! ### The power series -/

/-- The closed form c(n) = 2⌊(n+1)/4⌋ + ((n+1) mod 2). -/
def A106249_c (n : ℕ) : ℕ := 2 * ((n + 1) / 4) + (n + 1) % 2

noncomputable def A106249_num : PowerSeries ℚ := 1 - PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3

noncomputable def A106249_den : PowerSeries ℚ :=
  (1 + PowerSeries.X) * (1 + PowerSeries.X ^ 2) * (1 - PowerSeries.X) ^ 2

theorem A106249_den_eq : A106249_den = 1 - PowerSeries.X - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by
  rw [A106249_den]; ring

theorem A106249_series :
    A106249_num * A106249_den⁻¹ = PowerSeries.mk (fun n => (A106249_c n : ℚ)) := by
  have hc : PowerSeries.constantCoeff A106249_den ≠ 0 := by
    rw [A106249_den_eq]; simp
  symm
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hc, A106249_den_eq]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, A106249_num, PowerSeries.coeff_one, PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow]
  rw [show PowerSeries.mk (fun n => (A106249_c n : ℚ)) * PowerSeries.X =
    PowerSeries.mk (fun n => (A106249_c n : ℚ)) * PowerSeries.X ^ 1 by rw [pow_one],
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [A106249_c] <;> norm_num
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 5 := ⟨n - 5, by omega⟩
    simp only [show 1 ≤ r + 5 by omega, show 4 ≤ r + 5 by omega, show 5 ≤ r + 5 by omega,
      ↓reduceIte, show r + 5 ≠ 0 by omega, show r + 5 ≠ 1 by omega, show r + 5 ≠ 2 by omega,
      show r + 5 ≠ 3 by omega]
    have e : (A106249_c (r + 5) : ℚ) - A106249_c (r + 5 - 1) - A106249_c (r + 5 - 4) +
        A106249_c (r + 5 - 5) = 0 := by
      have h1 : A106249_c (r + 5) = A106249_c (r + 5 - 4) + 2 := by
        simp only [A106249_c]; omega
      have h2 : A106249_c (r + 5 - 1) = A106249_c (r + 5 - 5) + 2 := by
        simp only [A106249_c]; omega
      rw [h1, h2]; push_cast; ring
    simp only [A106249_c] at e ⊢
    linarith

/-! ### The roots of z^m = -1 -/

/-- ζ_j = exp(iπ(2j+1)/m). -/
noncomputable def A106249_zeta (m j : ℕ) : ℂ := exp (((2 * j + 1) * π / m : ℝ) * I)

theorem A106249_zeta_pow (m j : ℕ) (hm : 0 < m) : A106249_zeta m j ^ m = -1 := by
  rw [A106249_zeta, ← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * ((((2 * j + 1) * π / m : ℝ)) * I) = (j : ℂ) * (2 * π * I) + π * I := by
    push_cast; field_simp
  rw [this, Complex.exp_add, exp_nat_mul_two_pi_mul_I, exp_pi_mul_I, one_mul]

theorem A106249_zeta_injOn (m : ℕ) (hm : 0 < m) :
    Set.InjOn (A106249_zeta m) (Finset.range m : Set ℕ) := by
  intro j hj j' hj' he
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  rw [A106249_zeta, A106249_zeta, exp_eq_exp_iff_exists_int] at he
  obtain ⟨k, hk⟩ := he
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  /- (θ - θ' - 2πk) I = 0 -/
  have h0 : (((((2 * j + 1) * π / m : ℝ) - ((2 * j' + 1) * π / m : ℝ) - 2 * π * k : ℝ) : ℂ)) *
      I = 0 := by
    push_cast at hk ⊢; linear_combination hk
  have h0' : (((2 * j + 1) * π / m : ℝ) - ((2 * j' + 1) * π / m : ℝ) - 2 * π * k : ℝ) = 0 :=
    Complex.ofReal_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right I_ne_zero)
  have hpi : 0 < π := Real.pi_pos
  have e : ((j : ℝ) - j') = (k : ℝ) * m := by
    have : (((2 * j + 1) * π / m : ℝ) - ((2 * j' + 1) * π / m : ℝ)) * m = 2 * π * k * m := by
      linarith [congrArg (· * (m : ℝ)) h0']
    rw [sub_mul, div_mul_cancel₀ _ hmR, div_mul_cancel₀ _ hmR] at this
    have : π * (2 * ((j : ℝ) - j')) = π * (2 * (k * m)) := by linarith
    have := mul_left_cancel₀ hpi.ne' this
    linarith
  have e' : ((j : ℤ) - j') = k * m := by exact_mod_cast e
  /- |j - j'| < m forces k = 0 -/
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · have : k * (m : ℤ) ≤ -m := by nlinarith
      omega
    · exact h
    · have : (m : ℤ) ≤ k * m := by nlinarith
      omega
  subst hk0
  omega

theorem A106249_roots (m : ℕ) (hm : 0 < m) :
    (Finset.range m).image (A106249_zeta m) = Polynomial.nthRootsFinset m (-1 : ℂ) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨j, -, rfl⟩ := hz
    rw [Polynomial.mem_nthRootsFinset hm]
    exact A106249_zeta_pow m j hm
  · rw [Finset.card_image_of_injOn (A106249_zeta_injOn m hm), Finset.card_range,
      Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m _)

/-- cos θ < 0 for θ ∈ (0, 2π) iff θ ∈ (π/2, 3π/2). -/
theorem A106249_cos_neg_iff (θ : ℝ) (h0 : 0 < θ) (h2 : θ < 2 * π) :
    Real.cos θ < 0 ↔ π / 2 < θ ∧ θ < 3 * π / 2 := by
  constructor
  · intro hc
    by_contra hn
    rcases not_and_or.1 hn with h | h
    · push Not at h
      have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h⟩
      linarith
    · push Not at h
      have := Real.cos_nonneg_of_mem_Icc (x := θ - 2 * π) ⟨by linarith, by linarith [Real.pi_pos]⟩
      rw [Real.cos_sub_two_pi] at this
      linarith
  · rintro ⟨h1, h3⟩
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)

theorem A106249_count (m : ℕ) (hm : 0 < m) :
    ((Polynomial.nthRootsFinset m (-1 : ℂ)).filter (fun z => z.re < 0)).card =
      2 * (m / 4) + m % 2 := by
  classical
  rw [← A106249_roots m hm, Finset.filter_image,
    Finset.card_image_of_injOn ((A106249_zeta_injOn m hm).mono (fun x hx => by
      simp only [Finset.coe_filter, Finset.coe_range, Set.mem_Iio] at hx ⊢
      exact Finset.mem_range.1 hx.1))]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : (Finset.range m).filter (fun j => (A106249_zeta m j).re < 0) =
      Finset.Ico ((m + 2) / 4) ((3 * m + 1) / 4) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, A106249_zeta,
      exp_ofReal_mul_I_re]
    constructor
    · rintro ⟨hj, hc⟩
      have hθ0 : 0 < (2 * j + 1) * π / m := by positivity
      have hθ2 : (2 * j + 1) * π / m < 2 * π := by
        rw [div_lt_iff₀ hmR]
        have : (2 * (j : ℝ) + 1) < 2 * m := by
          have : 2 * j + 1 < 2 * m := by omega
          exact_mod_cast this
        nlinarith [Real.pi_pos]
      obtain ⟨h1, h3⟩ := (A106249_cos_neg_iff _ hθ0 hθ2).1 hc
      rw [lt_div_iff₀ hmR] at h1
      rw [div_lt_iff₀ hmR] at h3
      have h1' : (m : ℝ) < 2 * (2 * j + 1) := by nlinarith [Real.pi_pos]
      have h3' : 2 * (2 * (j : ℝ) + 1) < 3 * m := by nlinarith [Real.pi_pos]
      have a1 : m < 2 * (2 * j + 1) := by exact_mod_cast h1'
      have a3 : 2 * (2 * j + 1) < 3 * m := by exact_mod_cast h3'
      omega
    · rintro ⟨h1, h3⟩
      have a1 : m < 2 * (2 * j + 1) := by omega
      have a3 : 2 * (2 * j + 1) < 3 * m := by omega
      have hj : j < m := by omega
      refine ⟨hj, ?_⟩
      have h1' : (m : ℝ) < 2 * (2 * j + 1) := by exact_mod_cast a1
      have h3' : 2 * (2 * (j : ℝ) + 1) < 3 * m := by exact_mod_cast a3
      have hθ0 : 0 < (2 * j + 1) * π / m := by positivity
      have hθ2 : (2 * j + 1) * π / m < 2 * π := by
        rw [div_lt_iff₀ hmR]; nlinarith [Real.pi_pos]
      refine (A106249_cos_neg_iff _ hθ0 hθ2).2 ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hmR]; nlinarith [Real.pi_pos]
      · rw [div_lt_iff₀ hmR]; nlinarith [Real.pi_pos]
  rw [hs, Nat.card_Ico]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ m = 4 * q + r := ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r <;> omega

theorem A106249_main :
    (∀ n : ℕ, PowerSeries.coeff n (A106249_num * A106249_den⁻¹) =
      (((Polynomial.nthRootsFinset (n + 1) (-1 : ℂ)).filter (fun z => z.re < 0)).card : ℚ)) ∧
    PowerSeries.coeff 1 (A106249_num * A106249_den⁻¹) = 0 ∧
    ((Polynomial.nthRootsFinset 1 (-1 : ℂ)).filter (fun z => z.re < 0)).card = 1 := by
  refine ⟨fun n => ?_, ?_, ?_⟩
  · rw [A106249_series, PowerSeries.coeff_mk, A106249_count (n + 1) (by omega), A106249_c]
  · rw [A106249_series, PowerSeries.coeff_mk]; simp [A106249_c]
  · rw [A106249_count 1 (by norm_num)]
