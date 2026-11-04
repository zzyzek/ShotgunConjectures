/-
OEIS A210826, Mathlib proof.

A210826 is defined by the Lambert series
  sum_{n ≥ 1} a(n) x^n / (1 - x^n) = sum_{n ≥ 1} x^(n^3).
Comparing coefficients of x^m, this says sum_{d ∣ m} a(d) = [m is a cube]
for m ≥ 1 (the inverse Möbius transform of a is A010057). That coefficient
identity is the hypothesis `ha` below.

Main theorem `A210826_main`: every arithmetic function a : ℕ → ℤ with
sum_{d ∣ n} a(d) = [n is a cube] for all n ≥ 1 satisfies
- a is multiplicative (`ArithmeticFunction.IsMultiplicative`),
- a = μ * (cube indicator) (Dirichlet convolution),
- a(p^e) = -1 + ((e + 2) mod 3) for every prime p and e ≥ 0,
- its L-series is ζ(3s)/ζ(s) for Re s > 1 (Mathlib `LSeries`, `riemannZeta`).
This is Mathar's conjecture in the README (multiplicative, Dirichlet g.f.
ζ(3s)/ζ(s), inverse Möbius transform A010057) plus Cloitre's prime-power
formula.

Main theorem from the OEIS definition, `A210826_lambert_main`: for every
a : ℕ → ℤ (an `ArithmeticFunction ℤ`) satisfying the Lambert series
identity in ℚ⟦X⟧ with the X-adic (coefficientwise) topology
`PowerSeries.WithPiTopology`, stated as: the families
  n ↦ a(n+1) X^(n+1) (1 - X^(n+1))⁻¹   and   n ↦ X^((n+1)^3)
have the same sum S (`HasSum`), the four conclusions above hold.
`A210826_divisor_sum` does the coefficient extraction: the x^m coefficient
of the Lambert side is Σ_{d ∣ m} a(d), of the cube side [m is a cube].
Nothing is outside Lean.
-/
import Mathlib

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

open scoped Classical in
/-- The cube indicator (OEIS A010057, restricted to n ≥ 1): 1 if n ≥ 1 is a cube. -/
noncomputable def A210826_cube : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∃ m : ℕ, m ^ 3 = n then 1 else 0, by simp⟩

open scoped Classical in
theorem A210826_cube_apply (n : ℕ) :
    A210826_cube n = if n ≠ 0 ∧ ∃ m : ℕ, m ^ 3 = n then 1 else 0 := by
  rfl

theorem A210826_cube_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    A210826_cube (p ^ k) = if 3 ∣ k then 1 else 0 := by
  classical
  rw [A210826_cube_apply]
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  by_cases h3 : 3 ∣ k
  · obtain ⟨j, rfl⟩ := h3
    rw [ite_eq_left ⟨hne, ⟨p ^ j, by ring⟩⟩, ite_eq_left ⟨j, rfl⟩]
  · rw [ite_eq_right h3, ite_eq_right]
    rintro ⟨-, m, hm⟩
    have hdvd : m ∣ p ^ k := ⟨m ^ 2, by rw [← hm]; ring⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [← pow_mul] at hm
    exact h3 ⟨i, (Nat.pow_right_injective hp.two_le hm).symm.trans (by ring)⟩

theorem A210826_cube_mult : A210826_cube.IsMultiplicative := by
  refine ⟨by rw [A210826_cube_apply]; simp, ?_⟩
  intro m n hmn
  classical
  simp only [A210826_cube_apply]
  by_cases h0 : m * n = 0
  · rcases mul_eq_zero.mp h0 with h | h <;> simp [h]
  have hm : m ≠ 0 := left_ne_zero_of_mul h0
  have hn : n ≠ 0 := right_ne_zero_of_mul h0
  have hu : IsUnit (gcd m n) := by
    rw [show gcd m n = Nat.gcd m n from rfl, hmn]
    exact isUnit_one
  by_cases hc : ∃ c : ℕ, c ^ 3 = m * n
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨x, hx⟩ := exists_eq_pow_of_mul_eq_pow hu hc.symm
    have hu' : IsUnit (gcd n m) := by
      rw [show gcd n m = Nat.gcd n m from rfl, Nat.gcd_comm, hmn]
      exact isUnit_one
    obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hu' (by rw [mul_comm]; exact hc.symm)
    rw [ite_eq_left ⟨h0, c, hc⟩, ite_eq_left ⟨hm, x, hx.symm⟩, ite_eq_left ⟨hn, y, hy.symm⟩]
    simp
  · rw [ite_eq_right (fun h => hc h.2)]
    by_cases hmc : ∃ x : ℕ, x ^ 3 = m
    · by_cases hnc : ∃ y : ℕ, y ^ 3 = n
      · obtain ⟨x, rfl⟩ := hmc
        obtain ⟨y, rfl⟩ := hnc
        exact absurd ⟨x * y, by ring⟩ hc
      · simp [hnc]
    · simp [hmc]

theorem A210826_eq (a : ArithmeticFunction ℤ)
    (ha : ∀ n > 0, ∑ d ∈ n.divisors, a d = A210826_cube n) : a = μ * A210826_cube := by
  have h1 : a * ζ = A210826_cube := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [coe_mul_zeta_apply, ha n hn]
  calc a = a * ((ζ : ArithmeticFunction ℤ) * μ) := by rw [coe_zeta_mul_moebius, mul_one]
    _ = μ * A210826_cube := by rw [← mul_assoc, h1, mul_comm]

theorem A210826_prime_pow (a : ArithmeticFunction ℤ)
    (ha : ∀ n > 0, ∑ d ∈ n.divisors, a d = A210826_cube n) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    a (p ^ e) = -1 + (((e + 2) % 3 : ℕ) : ℤ) := by
  have hs : ∀ k, ∑ i ∈ Finset.range (k + 1), a (p ^ i) = if 3 ∣ k then 1 else 0 := by
    intro k
    rw [← Nat.sum_divisors_prime_pow hp, ha _ (pow_pos hp.pos k), A210826_cube_prime_pow hp]
  rcases e with _ | e
  · have := hs 0
    simp at this
    simp [this]
  · have h1 := hs (e + 1)
    rw [Finset.sum_range_succ, hs e] at h1
    have hm : (e + 1 + 2) % 3 = e % 3 := by omega
    rw [hm]
    have : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [ite_eq_left (by omega : 3 ∣ e), ite_eq_right (by omega : ¬ 3 ∣ e + 1)] at h1
      rw [h]; push_cast; linarith
    · rw [ite_eq_right (by omega : ¬ 3 ∣ e), ite_eq_right (by omega : ¬ 3 ∣ e + 1)] at h1
      rw [h]; push_cast; linarith
    · rw [ite_eq_right (by omega : ¬ 3 ∣ e), ite_eq_left (by omega : 3 ∣ e + 1)] at h1
      rw [h]; push_cast; linarith


open LSeries in
theorem A210826_LSeries_cube {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (A210826_cube n : ℂ)) s = riemannZeta (3 * s) := by
  have h3 : 1 < (3 * s).re := by
    simp only [Complex.mul_re]
    norm_num
    linarith
  rw [← LSeries_one_eq_riemannZeta h3, LSeries, LSeries]
  have hinj : Function.Injective (fun m : ℕ => m ^ 3) := Nat.pow_left_injective (by norm_num)
  rw [← hinj.tsum_eq]
  · congr 1
    funext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have hm3 : m ^ 3 ≠ 0 := pow_ne_zero _ hm
      rw [term_of_ne_zero hm3, term_of_ne_zero hm, A210826_cube_apply,
        ite_eq_left ⟨hm3, m, rfl⟩]
      have : (m : ℂ) ^ (3 * s) = ((m : ℂ) ^ 3) ^ s := by
        have := Complex.natCast_cpow_natCast_mul m 3 s
        push_cast at this
        exact this
      simp [this]
  · intro n hn
    rw [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hn
    · rw [term_of_ne_zero hn0, A210826_cube_apply] at hn
      by_cases h : n ≠ 0 ∧ ∃ m : ℕ, m ^ 3 = n
      · obtain ⟨m, hm⟩ := h.2
        exact ⟨m, hm⟩
      · rw [ite_eq_right h] at hn
        simp at hn

open LSeries in
theorem A210826_LSeries (a : ArithmeticFunction ℤ)
    (ha : ∀ n > 0, ∑ d ∈ n.divisors, a d = A210826_cube n) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (a n : ℂ)) s = riemannZeta (3 * s) / riemannZeta s := by
  have hcoe : (fun n => (a n : ℂ)) =
      ⇑((μ : ArithmeticFunction ℂ) * (A210826_cube : ArithmeticFunction ℂ)) := by
    funext n
    rw [← intCoe_mul, ← A210826_eq a ha, intCoe_apply]
  have hμ : LSeriesSummable (fun n => ((μ : ArithmeticFunction ℂ) n)) s := by
    simpa using LSeriesSummable_moebius_iff.mpr hs
  have hc : LSeriesSummable (fun n => ((A210826_cube : ArithmeticFunction ℂ) n)) s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hs
    rw [intCoe_apply, A210826_cube_apply]
    split_ifs <;> simp
  rw [hcoe, LSeries_mul' hμ hc]
  have hμL : LSeries (fun n => ((μ : ArithmeticFunction ℂ) n)) s = (riemannZeta s)⁻¹ := by
    have h1 := LSeries_zeta_mul_Lseries_moebius hs
    rw [LSeries_zeta_eq_riemannZeta hs] at h1
    exact eq_inv_of_mul_eq_one_right (by simpa using h1)
  have hcL : LSeries (fun n => ((A210826_cube : ArithmeticFunction ℂ) n)) s =
      riemannZeta (3 * s) := by
    simpa using A210826_LSeries_cube hs
  rw [hμL, hcL, div_eq_mul_inv, mul_comm]


theorem A210826_main (a : ArithmeticFunction ℤ)
    (ha : ∀ n > 0, ∑ d ∈ n.divisors, a d = A210826_cube n) :
    a.IsMultiplicative ∧
    a = μ * A210826_cube ∧
    (∀ p e : ℕ, p.Prime → a (p ^ e) = -1 + (((e + 2) % 3 : ℕ) : ℤ)) ∧
    (∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (a n : ℂ)) s = riemannZeta (3 * s) / riemannZeta s) := by
  refine ⟨?_, A210826_eq a ha, fun p e hp => A210826_prime_pow a ha hp e,
    fun s hs => A210826_LSeries a ha hs⟩
  rw [A210826_eq a ha]
  exact isMultiplicative_moebius.mul A210826_cube_mult

/-! ## The Lambert series definition

The OEIS definition, as an identity of formal power series over ℚ in the
X-adic (coefficientwise, `PowerSeries.WithPiTopology`) topology:
  Σ_{n ≥ 1} a(n) X^n (1 - X^n)⁻¹ = Σ_{n ≥ 1} X^(n^3),
written as: both families have sum S, for some S. -/

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Σ_{j ≥ 0} X^(kj) as a power series. -/
noncomputable def A210826_geom (k : ℕ) : PowerSeries ℚ := PowerSeries.mk fun m => if k ∣ m then 1 else 0

theorem A210826_dvd_sub_iff {k m : ℕ} (h : k ≤ m) : k ∣ m - k ↔ k ∣ m := by
  rw [← Nat.dvd_add_right (dvd_refl k), Nat.add_sub_cancel' h]

theorem A210826_geom_inv (k : ℕ) (hk : 0 < k) : ((1 : PowerSeries ℚ) - X ^ k)⁻¹ = A210826_geom k := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hk.ne'])]
  ext m
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one, A210826_geom, coeff_mk]
  by_cases hm : m = 0
  · subst hm; simp [Nat.not_le.2 hk]
  · by_cases h2 : k ≤ m
    · simp [hm, h2, coeff_mk, A210826_dvd_sub_iff h2]
    · have h1 : ¬ k ∣ m := fun h => h2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h)
      simp [hm, h1, h2]

/-- The n-th Lambert term a(n+1) X^(n+1) (1 - X^(n+1))⁻¹. -/
noncomputable def A210826_lterm (a : ℕ → ℤ) (n : ℕ) : PowerSeries ℚ :=
  C (a (n + 1) : ℚ) * X ^ (n + 1) * ((1 : PowerSeries ℚ) - X ^ (n + 1))⁻¹

theorem A210826_coeff_lterm (a : ℕ → ℤ) (n m : ℕ) (hm : 0 < m) :
    coeff m (A210826_lterm a n) = if n + 1 ∣ m then (a (n + 1) : ℚ) else 0 := by
  rw [A210826_lterm, A210826_geom_inv _ (Nat.succ_pos n), mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', A210826_geom, coeff_mk]
  by_cases h2 : n + 1 ≤ m
  · simp [h2, A210826_dvd_sub_iff h2]
  · have h1 : ¬ n + 1 ∣ m := fun h => h2 (Nat.le_of_dvd hm h)
    simp [h1, h2]

open scoped Classical in
/-- Coefficient extraction: the Lambert identity gives Σ_{d ∣ m} a(d) = [m is a cube]. -/
theorem A210826_divisor_sum (a : ℕ → ℤ) (S : PowerSeries ℚ)
    (hL : HasSum (A210826_lterm a) S) (hC : HasSum (fun n : ℕ => (X : PowerSeries ℚ) ^ ((n + 1) ^ 3)) S)
    (m : ℕ) (hm : 0 < m) :
    ∑ d ∈ m.divisors, a d = if m ≠ 0 ∧ ∃ k : ℕ, k ^ 3 = m then 1 else 0 := by
  have hL' := ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).1 hL) m
  have hC' := ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).1 hC) m
  /- the Lambert side: finitely many nonzero terms n < m -/
  have h1 : HasSum (fun n => coeff m (A210826_lterm a n))
      (∑ n ∈ Finset.range m, if n + 1 ∣ m then (a (n + 1) : ℚ) else 0) := by
    have hf : (fun n => coeff m (A210826_lterm a n)) =
        fun n => if n + 1 ∣ m then (a (n + 1) : ℚ) else 0 :=
      funext fun n => A210826_coeff_lterm a n m hm
    rw [hf]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have : ¬ n + 1 ∣ m := fun hd => by have := Nat.le_of_dvd hm hd; omega
    simp [this]
  have hsumL : (∑ n ∈ Finset.range m, if n + 1 ∣ m then (a (n + 1) : ℚ) else 0) =
      ((∑ d ∈ m.divisors, a d : ℤ) : ℚ) := by
    push_cast
    rw [Nat.divisors, Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm 1]
  /- the cube side -/
  have h2 : HasSum (fun n : ℕ => coeff m ((X : PowerSeries ℚ) ^ ((n + 1) ^ 3)))
      (∑ n ∈ Finset.range m, if m = (n + 1) ^ 3 then (1 : ℚ) else 0) := by
    have hf : (fun n : ℕ => coeff m ((X : PowerSeries ℚ) ^ ((n + 1) ^ 3))) =
        fun n => if m = (n + 1) ^ 3 then (1 : ℚ) else 0 := funext fun n => coeff_X_pow _ _
    rw [hf]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have : m ≠ (n + 1) ^ 3 := fun he => by
      have : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
    simp [this]
  have hsumC : (∑ n ∈ Finset.range m, if m = (n + 1) ^ 3 then (1 : ℚ) else 0) =
      ((if m ≠ 0 ∧ ∃ k : ℕ, k ^ 3 = m then 1 else 0 : ℤ) : ℚ) := by
    by_cases hcube : ∃ k : ℕ, k ^ 3 = m
    · obtain ⟨k, rfl⟩ := hcube
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hm
        · exact h
      have hc : (k ^ 3 ≠ 0 ∧ ∃ k' : ℕ, k' ^ 3 = k ^ 3) := ⟨hm.ne', k, rfl⟩
      simp only [hc]
      rw [Finset.sum_eq_single (k - 1)]
      · simp [Nat.sub_add_cancel hk, hk.ne']
      · intro n _ hn
        have : k ^ 3 ≠ (n + 1) ^ 3 := fun he => hn (by
          have := (Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)) he
          omega)
        simp [this]
      · intro hn
        exfalso; apply hn
        rw [Finset.mem_range]
        have : k ≤ k ^ 3 := Nat.le_self_pow (by norm_num) _
        omega
    · have hc : ¬ (m ≠ 0 ∧ ∃ k : ℕ, k ^ 3 = m) := fun h => hcube h.2
      simp only [hc, ↓reduceIte, Int.cast_zero]
      apply Finset.sum_eq_zero
      intro n _
      have : m ≠ (n + 1) ^ 3 := fun he => hcube ⟨n + 1, he.symm⟩
      simp [this]
  have := (hL'.unique h1).symm.trans (hC'.unique h2)
  rw [hsumL, hsumC] at this
  exact_mod_cast this

/-- Main theorem from the Lambert series definition. -/
theorem A210826_lambert_main (a : ArithmeticFunction ℤ) (S : PowerSeries ℚ)
    (hL : HasSum (A210826_lterm a) S)
    (hC : HasSum (fun n : ℕ => (X : PowerSeries ℚ) ^ ((n + 1) ^ 3)) S) :
    a.IsMultiplicative ∧
    a = μ * A210826_cube ∧
    (∀ p e : ℕ, p.Prime → a (p ^ e) = -1 + (((e + 2) % 3 : ℕ) : ℤ)) ∧
    (∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (a n : ℂ)) s = riemannZeta (3 * s) / riemannZeta s) := by
  apply A210826_main
  intro n hn
  rw [A210826_divisor_sum a S hL hC n hn, A210826_cube_apply]
