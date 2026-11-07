import Mathlib
import OpenProblemsLib.BernoulliDen

/-
OEIS A141459: a(n) = product of the odd primes p with p - 1 | n (a(0) = 1).
Conjecture (J.-F. Alcover, 2013): a(n) = denominator of ∫_0^1 log(1 - 1/x)^n dx.
OEIS A211163: numerator of (-1/π^n) ∫_0^1 log(1 - 1/x)^n dx (n ≥ 2); conjecture: the
denominators are A141459.

Reading. log is the principal complex logarithm (1 - 1/x < 0 on (0,1)); the integral is
q_n (π i)^n with q_n rational, and "denominator" means the denominator of q_n.

Main theorems.
* `integral_formula n : ∫ x in 0..1, log(1 - 1/x)^n = (2^n B'_n) (π i)^n` (B' = `bernoulli'`).
* `A141459_eq_den n : (2^n B'_n).den = A141459 n`.
* `A141459_conjecture n q : ∫ ... = q (π i)^n → q.den = A141459 n`.
* `A211163_conjecture n (2 ≤ n) r : (-1/π^n) ∫ ... = r → r.den = A141459 n`.

Route.
* `change_of_variables`: x = 1/(1+e^t) gives ∫_ℝ ρ(t) (t + π i)^n dt with the logistic
  density ρ(t) = e^t/(1+e^t)^2 (log(-e^t) = t + π i).
* Moments μ_j = ∫ ρ t^j: μ_0 = 1 (`moment_zero`), μ_odd = 0 (`moment_odd`),
  μ_2k = 2 ∫_0^∞ = 2 (2k)! η(2k) via ρ(s) = Σ (-1)^(m+1) m e^(-ms) and Γ integrals
  (`moment_series`, `eta_hasSum`), with ζ(2k) from Mathlib's `hasSum_zeta_nat`;
  uniformly μ_j = -(2^j - 2) B'_j (π i)^j (`moment_formula`).
* `bern_identity`: Σ_j C(n,j)(2 - 2^j) B'_j = 2^n B'_n (exponential generating functions).
* `den_two_pow_bernoulli`: von Staudt–Clausen (Mathlib's `Bernoulli.vonStaudt_clausen`,
  `padicValRat_bernoulli`; library `OpenProblemsLib.BernoulliDen.bernoulli_den_not_dvd`)
  gives the p-adic valuations of 2^(2k) B_2k.
Checked: all of the above. Not checked: nothing beyond the reading. Axioms: propext,
Classical.choice, Quot.sound.
-/

namespace OEIS_A141459

open OpenProblemsLib.BernoulliDen


section
open Finset

/-- A141459: product of the odd primes p with p - 1 ∣ n (a(0) = 1). -/
def A141459 (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∏ p ∈ (range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ n), p

theorem den_vp (x : ℚ) (p : ℕ) [hp : Fact p.Prime] :
    (padicValNat p x.den : ℤ) = max 0 (-padicValRat p x) := by
  rw [padicValRat_def]
  by_cases h : p ∣ x.den
  · have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro h'
      have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp h'
      exact Nat.not_coprime_of_dvd_of_dvd hp.out.one_lt h1 h x.reduced
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    simp
  · rw [padicValNat.eq_zero_of_not_dvd h]
    simp

theorem bernoulli_ne_zero (k : ℕ) (hk : 0 < k) : bernoulli (2 * k) ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have := Bernoulli.padicValRat_bernoulli (p := 2) hk (by norm_num)
  rw [h] at this; simp at this

theorem den_two_pow_bernoulli (k : ℕ) (hk : 0 < k) :
    ((2 : ℚ) ^ (2 * k) * bernoulli (2 * k)).den =
      ∏ p ∈ (range (2 * k + 2)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ 2 * k), p := by
  set x := (2 : ℚ) ^ (2 * k) * bernoulli (2 * k) with hx
  set T := (range (2 * k + 2)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ 2 * k) with hT
  have hB := bernoulli_ne_zero k hk
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hB
  have hP0 : ∏ p ∈ T, p ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p hp => (Finset.mem_filter.mp hp).2.1.ne_zero)
  apply Nat.eq_of_factorization_eq x.den_ne_zero hP0
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_prod (fun q hq => (Finset.mem_filter.mp hq).2.1.ne_zero)]
    rw [Finsupp.finsetSum_apply]
    have hR : ∑ q ∈ T, q.factorization p = if p ∈ T then 1 else 0 := by
      rw [Finset.sum_congr rfl (fun q hq => by
        rw [(Finset.mem_filter.mp hq).2.1.factorization, Finsupp.single_apply])]
      rw [Finset.sum_ite_eq']
    rw [hR]
    have hv := den_vp x p
    have hvx : padicValRat p x = 2 * k * padicValRat p 2 + padicValRat p (bernoulli (2 * k)) := by
      rw [hx, padicValRat.mul (pow_ne_zero _ (by norm_num)) hB, padicValRat.pow]; push_cast; ring
    by_cases h2 : p = 2
    · subst h2
      have hT2 : (2 : ℕ) ∉ T := by simp [hT]
      rw [ite_eq_right hT2]
      rw [Bernoulli.padicValRat_bernoulli hk (by norm_num), show padicValRat 2 2 = 1 by
        simpa using padicValRat.self (p := 2) (by norm_num)] at hvx
      have : (padicValNat 2 x.den : ℤ) = 0 := by rw [hv, hvx]; simp; omega
      exact_mod_cast this
    · have hv2 : padicValRat p 2 = 0 := by
        have : padicValRat p ((2 : ℕ) : ℚ) = padicValNat p 2 := (padicValRat_of_nat 2).symm
        rw [show ((2 : ℕ) : ℚ) = 2 by norm_num] at this
        rw [this, padicValNat.eq_zero_of_not_dvd]; · rfl
        intro hd
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
      by_cases hpk : (p - 1) ∣ 2 * k
      · have hpT : p ∈ T := by
          simp only [hT, Finset.mem_filter, Finset.mem_range]
          exact ⟨by have := Nat.le_of_dvd (by omega) hpk; omega, hp, h2, hpk⟩
        rw [ite_eq_left hpT]
        rw [hv2, Bernoulli.padicValRat_bernoulli hk hpk] at hvx
        have : (padicValNat p x.den : ℤ) = 1 := by rw [hv, hvx]; simp
        exact_mod_cast this
      · have hpT : p ∉ T := by simp [hT, hpk]
        rw [ite_eq_right hpT]
        have hnd := bernoulli_den_not_dvd k p hpk
        have hB0 : 0 ≤ padicValRat p (bernoulli (2 * k)) := by
          rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hnd]; simp
        rw [hv2] at hvx
        have : (padicValNat p x.den : ℤ) = 0 := by rw [hv, hvx]; simp; omega
        exact_mod_cast this
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

theorem A141459_eq_den (n : ℕ) : ((2 : ℚ) ^ n * bernoulli' n).den = A141459 n := by
  unfold A141459
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ite_eq_right (by omega)]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show k + k = 2 * k by ring, bernoulli'_eq_bernoulli, Even.neg_one_pow ⟨k, by ring⟩, one_mul]
    exact den_two_pow_bernoulli k (by omega)
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [bernoulli'_one]
    · rw [bernoulli'_eq_zero_of_odd ⟨k, rfl⟩ (by omega), mul_zero, Rat.den_zero]
      symm
      apply Finset.prod_eq_one
      intro p hp
      exfalso
      obtain ⟨_, hpr, hp2, hd⟩ := (Finset.mem_filter.mp hp)
      have hodd : Odd p := hpr.odd_of_ne_two hp2
      obtain ⟨u, hu⟩ := hodd
      obtain ⟨v, hv⟩ := hd
      have : 2 * k + 1 = 2 * (u * v) := by rw [hv, hu]; simp; ring
      omega



end

section
open PowerSeries Finset Nat
/-- Σ_j C(n,j) (2 - 2^j) B'_j = 2^n B'_n -/
theorem bern_identity (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (2 - 2 ^ j) * bernoulli' j = 2 ^ n * bernoulli' n := by
  set B := bernoulli'PowerSeries ℚ
  set E := exp ℚ
  set B2 := rescale (2 : ℚ) B
  have h1 : B * (E - 1) = X * E := bernoulli'PowerSeries_mul_exp_sub_one ℚ
  have hE2 : rescale (2 : ℚ) E = E ^ 2 := by
    have := exp_pow_eq_rescale_exp (A := ℚ) 2; push_cast at this; exact this.symm
  have h2 : B2 * (E ^ 2 - 1) = (C (2 : ℚ) * X) * E ^ 2 := by
    have := congrArg (rescale (2 : ℚ)) h1
    rw [map_mul, map_mul, map_sub, map_one, rescale_X, hE2] at this
    exact this
  have hne : (E ^ 2 - 1 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    rw [← hE2, map_sub, coeff_rescale, coeff_exp, coeff_one] at this
    norm_num at this
  have key : E * (C (2 : ℚ) * B - B2) = B2 := by
    apply mul_right_cancel₀ hne
    linear_combination (C (2 : ℚ) * E * (E + 1)) * h1 - (E + 1) * h2
  have hc := congrArg (coeff n) key
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [B2, B, E, coeff_rescale, coeff_exp, map_sub, coeff_C_mul, bernoulli'PowerSeries,
    coeff_mk, Algebra.algebraMap_self, RingHom.id_apply] at hc
  have hfac : (n ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hc2 : ∑ x ∈ range (n + 1), (n.choose x : ℚ) * (2 - 2 ^ (n - x)) * bernoulli' (n - x) =
      2 ^ n * bernoulli' n := by
    have e : 2 ^ n * bernoulli' n = (2 ^ n * (bernoulli' n / (n ! : ℚ))) * n ! := by
      field_simp
    rw [e, ← hc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have hcf : (n.choose x : ℚ) * x ! * (n - x)! = n ! := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : x ≤ n)
    have h1 : (x ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos x).ne'
    have h2 : ((n - x)! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (n - x)).ne'
    rw [← hcf]
    field_simp
  rw [← hc2, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_range] at hx
  rw [show n + 1 - 1 - x = n - x by omega, Nat.choose_symm (by omega : x ≤ n)]

end

open Real MeasureTheory Set Filter Topology

/-- logistic density -/
noncomputable def rho (t : ℝ) : ℝ := exp t / (1 + exp t) ^ 2

theorem rho_neg (t : ℝ) : rho (-t) = rho t := by
  unfold rho
  rw [Real.exp_neg]
  have h := exp_pos t
  field_simp
  ring

theorem rho_nonneg (t : ℝ) : 0 ≤ rho t := by unfold rho; positivity

theorem rho_le (t : ℝ) : rho t ≤ exp (-|t|) := by
  unfold rho
  have h := exp_pos t
  rw [div_le_iff₀ (by positivity)]
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, Real.exp_neg]
    have : (exp t)⁻¹ * exp t = 1 := inv_mul_cancel₀ h.ne'
    have hi : 0 < (exp t)⁻¹ := inv_pos.mpr h
    nlinarith
  · rw [abs_of_neg ht, neg_neg]
    have : 1 ≤ (1 + exp t) ^ 2 := by nlinarith
    nlinarith

theorem integrable_comp_abs' {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have int_Ioi : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi int_Ioi
  have := int_Iic.union int_Ioi
  rw [Iic_union_Ioi, integrableOn_univ] at this
  exact this

theorem integrableOn_pow_exp (j : ℕ) : IntegrableOn (fun s : ℝ => exp (-s) * s ^ j) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := (j : ℝ) + 1) (by positivity)
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only
  rw [add_sub_cancel_right, Real.rpow_natCast]

theorem integrable_rho_pow (j : ℕ) : Integrable (fun t => rho t * t ^ j) := by
  have hg : Integrable (fun t : ℝ => (fun s => exp (-s) * s ^ j) |t|) :=
    integrable_comp_abs' (integrableOn_pow_exp j)
  refine hg.mono' (by unfold rho; fun_prop) (Eventually.of_forall (fun t => ?_))
  simp only
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (rho_nonneg t)]
  exact mul_le_mul_of_nonneg_right (rho_le t) (by positivity)


theorem moment_zero : ∫ t, rho t = 1 := by
  have hd : ∀ t, HasDerivAt (fun t => (1 + exp (-t))⁻¹) (rho t) t := by
    intro t
    have h1 : HasDerivAt (fun t => 1 + exp (-t)) (-exp (-t)) t := by
      have := ((hasDerivAt_neg t).exp).const_add 1
      simpa using this
    have h2 := h1.inv (by positivity)
    convert h2 using 1
    rw [← rho_neg t]; unfold rho; ring
  have hint : Integrable rho := by simpa using integrable_rho_pow 0
  have h := integral_of_hasDerivAt_of_tendsto hd hint (m := 0) (n := 1) ?_ ?_
  · rw [h]; ring
  · -- at -∞, exp(-t) → ∞
    have : Tendsto (fun t : ℝ => 1 + exp (-t)) atBot atTop :=
      tendsto_atTop_add_const_left _ 1 (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)
    exact tendsto_inv_atTop_zero.comp this
  · have : Tendsto (fun t : ℝ => 1 + exp (-t)) atTop (𝓝 (1 + 0)) :=
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_add 1
    rw [add_zero] at this
    simpa using this.inv₀ one_ne_zero

theorem moment_odd (j : ℕ) (hj : Odd j) : ∫ t, rho t * t ^ j = 0 := by
  have h : ∫ t, rho (-t) * (-t) ^ j = ∫ t, rho t * t ^ j :=
    integral_neg_eq_self (fun t => rho t * t ^ j) volume
  simp_rw [rho_neg, hj.neg_pow, mul_neg, integral_neg] at h
  linarith

theorem moment_even (k : ℕ) : ∫ t, rho t * t ^ (2 * k) = 2 * ∫ s in Ioi 0, rho s * s ^ (2 * k) := by
  rw [← integral_comp_abs (f := fun s => rho s * s ^ (2 * k))]
  congr 1; ext t
  rw [pow_mul, pow_mul, sq_abs]
  congr 1
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, rho_neg]


theorem integral_pow_exp_m (k m : ℕ) (hm : 1 ≤ m) :
    ∫ s in Ioi 0, exp (-(m * s)) * s ^ (2 * k) = (Nat.factorial (2 * k)) / (m : ℝ) ^ (2 * k + 1) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := ((2 * k : ℕ) : ℝ) + 1) (r := m) (by positivity) hm'
  rw [show ((2 * k : ℕ) : ℝ) + 1 = ((2 * k : ℕ) : ℝ) + 1 from rfl, Real.Gamma_nat_eq_factorial] at h
  have h2 : ∫ s in Ioi 0, exp (-(m * s)) * s ^ (2 * k) =
      ∫ t in Ioi (0 : ℝ), t ^ (((2 * k : ℕ) : ℝ) + 1 - 1) * exp (-(m * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
  rw [h2, h, show ((2 * k : ℕ) : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, div_pow, one_pow]
  ring

theorem rho_series (k : ℕ) (s : ℝ) (hs : 0 < s) :
    HasSum (fun m : ℕ => -((m : ℝ) * (-1) ^ m) * (exp (-(m * s)) * s ^ (2 * k)))
      (rho s * s ^ (2 * k)) := by
  have hr : ‖-exp (-s)‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    calc exp (-s) < exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).neg.mul_right (s ^ (2 * k))
  convert h using 1
  · ext m
    have e : (-exp (-s)) ^ m = (-1) ^ m * exp (-(m * s)) := by
      rw [neg_eq_neg_one_mul, mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [e]; ring
  · rw [← rho_neg s]; unfold rho; ring

theorem moment_series (k : ℕ) (hk : 1 ≤ k) :
    ∫ s in Ioi 0, rho s * s ^ (2 * k) =
      ∑' m : ℕ, -((m : ℝ) * (-1) ^ m) * ((Nat.factorial (2 * k)) / (m : ℝ) ^ (2 * k + 1)) := by
  set F : ℕ → ℝ → ℝ := fun m s => -((m : ℝ) * (-1) ^ m) * (exp (-(m * s)) * s ^ (2 * k)) with hF
  have hnF : ∀ m s, 0 < s → ‖F m s‖ = (m : ℝ) * (exp (-(m * s)) * s ^ (2 * k)) := by
    intro m s hs
    rw [hF]
    simp only
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      mul_one, Nat.abs_cast, abs_of_pos (exp_pos _), abs_of_pos (pow_pos hs _)]
  have hInt : ∀ m, Integrable (F m) (volume.restrict (Ioi 0)) := by
    intro m
    have hg : IntegrableOn (fun s : ℝ => (m : ℝ) * (exp (-s) * s ^ (2 * k))) (Ioi 0) :=
      (integrableOn_pow_exp (2 * k)).const_mul m
    refine hg.mono' (by rw [hF]; fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun s hs => ?_)
    rw [hnF m s hs]
    have hs' : 0 < s := hs
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
  have hnorm : ∀ m, ∫ s in Ioi 0, ‖F m s‖ = (Nat.factorial (2 * k)) * (1 / (m : ℝ) ^ (2 * k)) := by
    intro m
    have e : ∫ s in Ioi 0, ‖F m s‖ = ∫ s in Ioi 0, (m : ℝ) * (exp (-(m * s)) * s ^ (2 * k)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs => hnF m s hs)
    rw [e, integral_const_mul]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, zero_mul, zero_pow (by omega), div_zero, mul_zero]
    · rw [integral_pow_exp_m k m hm]
      have : (0 : ℝ) < m := by exact_mod_cast hm
      field_simp
      ring
  have hsum : Summable (fun m => ∫ s in Ioi 0, ‖F m s‖) := by
    simp_rw [hnorm]
    exact (Real.summable_one_div_nat_pow.mpr (by omega)).mul_left _
  have h := integral_tsum_of_summable_integral_norm hInt hsum
  have e1 : ∫ s in Ioi 0, rho s * s ^ (2 * k) = ∫ s in Ioi 0, ∑' m, F m s :=
    setIntegral_congr_fun measurableSet_Ioi (fun s hs => (rho_series k s (mem_Ioi.mp hs)).tsum_eq.symm)
  rw [e1, ← h]
  congr 1; ext m
  rw [hF]; simp only
  rw [integral_const_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [integral_pow_exp_m k m hm]

/-- ζ(2k) value from Mathlib -/
noncomputable def Zk (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (Nat.factorial (2 * k))

theorem eta_hasSum (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun m : ℕ => (-1 : ℝ) ^ (m + 1) * (1 / (m : ℝ) ^ (2 * k)))
      (Zk k - 2 * (Zk k / 2 ^ (2 * k))) := by
  have hZ : HasSum (fun m : ℕ => 1 / (m : ℝ) ^ (2 * k)) (Zk k) := hasSum_zeta_nat (by omega)
  set e : ℕ → ℝ := fun m => if Even m then 1 / (m : ℝ) ^ (2 * k) else 0 with he
  have hE : HasSum e (Zk k / 2 ^ (2 * k)) := by
    have h2 : HasSum (fun n : ℕ => 1 / ((2 * n : ℕ) : ℝ) ^ (2 * k)) (Zk k / 2 ^ (2 * k)) := by
      have := hZ.mul_left (1 / 2 ^ (2 * k))
      convert this using 1
      · ext n; push_cast; rw [mul_pow]; field_simp
      · ring
    have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by simp at h; exact h
    rw [← hinj.hasSum_iff]
    · convert h2 using 1
      ext n; simp [he]
    · intro m hm
      simp only [he]
      rw [ite_eq_right]
      rintro ⟨t, ht⟩; exact hm ⟨t, by simp; omega⟩
  convert hZ.sub (hE.mul_left 2) using 1
  ext m
  simp only [he]
  split_ifs with h
  · rw [pow_succ, h.neg_one_pow]; ring
  · rw [pow_succ, (Nat.not_even_iff_odd.mp h).neg_one_pow]; ring

theorem moment_even_value (k : ℕ) (hk : 1 ≤ k) :
    ∫ t, rho t * t ^ (2 * k) = (-1) ^ (k + 1) * (2 ^ (2 * k) - 2) * π ^ (2 * k) * bernoulli (2 * k) := by
  rw [moment_even, moment_series k hk]
  have h := (eta_hasSum k hk).mul_left ((Nat.factorial (2 * k)) : ℝ)
  have h' : HasSum (fun m : ℕ => -((m : ℝ) * (-1) ^ m) * ((Nat.factorial (2 * k)) / (m : ℝ) ^ (2 * k + 1)))
      ((Nat.factorial (2 * k)) * (Zk k - 2 * (Zk k / 2 ^ (2 * k)))) := by
    convert h using 1
    ext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, zero_mul, neg_zero, zero_pow (show 2 * k ≠ 0 by omega), div_zero,
        mul_zero]
    · have : (0 : ℝ) < m := by exact_mod_cast hm
      field_simp
      ring
  rw [h'.tsum_eq]
  unfold Zk
  have hf : ((Nat.factorial (2 * k)) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2]
  field_simp


open Complex in
theorem moment_formula (j : ℕ) :
    ((∫ t, rho t * t ^ j : ℝ) : ℂ) = -(((2 ^ j - 2) * bernoulli' j : ℚ) : ℂ) * (π * I) ^ j := by
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [moment_zero]; norm_num
    · rw [show k + k = 2 * k by ring, moment_even_value k hk,
        ← bernoulli_eq_bernoulli'_of_ne_one (by omega), mul_pow, pow_mul I, I_sq]
      push_cast
      ring
  · rw [moment_odd j hodd]
    rcases hodd with ⟨k, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [bernoulli'_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]; simp

noncomputable def sig (t : ℝ) : ℝ := (1 + exp t)⁻¹

open Complex in
theorem change_of_variables (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (Complex.log (1 - 1 / (x : ℂ))) ^ n =
      ∫ t, (rho t : ℂ) * ((t : ℂ) + π * I) ^ n := by
  have hd : ∀ t ∈ (univ : Set ℝ), HasDerivWithinAt sig (-rho t) univ t := by
    intro t _
    have h1 : HasDerivAt (fun t => 1 + Real.exp t) (Real.exp t) t := (Real.hasDerivAt_exp t).const_add 1
    have h2 : HasDerivAt sig (-(Real.exp t) / (1 + Real.exp t) ^ 2) t := h1.inv (by positivity)
    convert h2.hasDerivWithinAt using 1
    unfold rho; ring
  have hinj : InjOn sig univ := by
    intro a _ b _ h
    unfold sig at h
    have := inv_injective h
    simpa using this
  have himg : sig '' univ = Ioo 0 1 := by
    ext y
    simp only [mem_image, mem_univ, true_and, mem_Ioo]
    constructor
    · rintro ⟨t, rfl⟩
      unfold sig
      have := Real.exp_pos t
      constructor
      · positivity
      · rw [inv_lt_one₀ (by positivity)]; linarith
    · rintro ⟨h0, h1⟩
      refine ⟨Real.log (1 / y - 1), ?_⟩
      have hp : 0 < 1 / y - 1 := by rw [sub_pos, lt_div_iff₀ h0]; linarith
      unfold sig
      rw [Real.exp_log hp]
      field_simp
      ring
  have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (fun x : ℝ => (Complex.log (1 - 1 / (x : ℂ))) ^ n)
  rw [himg, setIntegral_univ] at hcv
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hcv]
  congr 1; ext t
  rw [abs_neg, abs_of_nonneg (rho_nonneg t), Complex.real_smul]
  congr 1
  unfold sig
  have he : (1 : ℂ) - 1 / (((1 + Real.exp t)⁻¹ : ℝ) : ℂ) = ((Real.exp t : ℝ) : ℂ) * (-1) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.log_ofReal_mul (Real.exp_pos t) (by norm_num), Real.log_exp, Complex.log_neg_one]

open Complex in
theorem integral_formula (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (Complex.log (1 - 1 / (x : ℂ))) ^ n =
      (((2 : ℚ) ^ n * bernoulli' n : ℚ) : ℂ) * (π * I) ^ n := by
  rw [change_of_variables]
  have e : ∀ t : ℝ, (rho t : ℂ) * ((t : ℂ) + π * I) ^ n =
      ∑ m ∈ Finset.range (n + 1), ((rho t * t ^ m : ℝ) : ℂ) * ((π * I) ^ (n - m) * (n.choose m)) := by
    intro t
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    push_cast; ring
  simp_rw [e]
  rw [integral_finsetSum]
  · rw [Finset.sum_congr rfl (fun m _ => by rw [integral_mul_const, integral_complex_ofReal, moment_formula m])]
    have hb := bern_identity n
    have hb' : (((2 : ℚ) ^ n * bernoulli' n : ℚ) : ℂ) =
        ∑ j ∈ Finset.range (n + 1), (((n.choose j : ℚ) * (2 - 2 ^ j) * bernoulli' j : ℚ) : ℂ) := by
      rw [← hb]; push_cast; rfl
    rw [hb', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    have : (π * I) ^ n = (π * I) ^ m * (π * I) ^ (n - m) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    push_cast; ring
  · intro m _
    exact ((integrable_rho_pow m).ofReal).mul_const _


open Complex in
/-- Conjecture of A141459 (Alcover): the integral is a rational multiple of (π i)^n, and the
denominator of that rational is A141459(n). -/
theorem A141459_conjecture (n : ℕ) (q : ℚ)
    (h : ∫ x in (0 : ℝ)..1, (Complex.log (1 - 1 / (x : ℂ))) ^ n = (q : ℂ) * (π * I) ^ n) :
    q.den = A141459 n := by
  rw [integral_formula] at h
  have hne : (π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero)
  have h2 := mul_right_cancel₀ hne h
  have h3 : (2 : ℚ) ^ n * bernoulli' n = q := by exact_mod_cast h2
  rw [← h3, A141459_eq_den]

open Complex in
/-- Conjecture of A211163 (Alcover): for n ≥ 2, (-1/π^n) ∫_0^1 log(1-1/x)^n dx is rational with
denominator A141459(n). -/
theorem A211163_conjecture (n : ℕ) (hn : 2 ≤ n) (r : ℚ)
    (h : (-1 / (π : ℂ) ^ n) * ∫ x in (0 : ℝ)..1, (Complex.log (1 - 1 / (x : ℂ))) ^ n = (r : ℂ)) :
    r.den = A141459 n := by
  rw [integral_formula] at h
  have hpi : (π : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have h2 : (r : ℂ) = -(((2 : ℚ) ^ n * bernoulli' n : ℚ) : ℂ) * I ^ n := by
    rw [← h, mul_pow]; field_simp
  rw [← A141459_eq_den]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · rw [hk, show k + k = 2 * k by ring, pow_mul I, I_sq] at h2
    have h3 : r = -((2 : ℚ) ^ n * bernoulli' n) * (-1) ^ k := by
      rw [hk, show k + k = 2 * k by ring]; exact_mod_cast h2
    rw [h3]
    rcases neg_one_pow_eq_or ℚ k with e | e <;> rw [e]
    · rw [mul_one, Rat.den_neg_eq_den]
    · rw [mul_neg_one, neg_neg]
  · rw [bernoulli'_eq_zero_of_odd hodd (by omega)] at h2 ⊢
    have h3 : r = 0 := by simpa using h2
    rw [h3]; simp

end OEIS_A141459

open OEIS_A141459
