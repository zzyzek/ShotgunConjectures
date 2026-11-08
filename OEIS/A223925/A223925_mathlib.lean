import Mathlib
import OpenProblemsLib.BernoulliDen

/-
OEIS A223925 (a(2n) = 4^n divides A132049(2n)), Mathlib proof.

Definitions: `sec = 1/cos`, `tan = sin/cos` in ℚ⟦X⟧ (Mathlib `PowerSeries.cos`, `sin`), as in
OEIS/A117414/A117414_mathlib.lean; tangent numbers `tangentNum m = (2m-1)! [x^(2m-1)] tan`
(A000182(m) = A000111(2m-1)); secant numbers `secNum m = (2m)! [x^(2m)] sec`
(A000364(m) = A000111(2m)); `A132049_even n` = numerator in lowest terms of 2(2n) T_n / E_n.

Main theorem `A223925_main`: for n >= 1, A132049(2n) = 4^n u with u odd; so 4^n divides it
(the conjecture) and v_2(A132049(2n)) = 2n.

Steps (Lean + Mathlib + lib OpenProblemsLib.BernoulliDen):
* `Dser_spec`, `R_eq`, `coeff_Xtan`, `tangentNum_eq`: T_m = (-1)^(m+1) B_{2m} (16^m - 4^m)/(2m),
  from x tanh x = B(4x) - B(2x) + x (B = e.g.f. of Bernoulli numbers) and D(i x) = -x tan x over ℂ.
* `den_dvd`, `genocchi_odd`: 2(4^m - 1) B_{2m} is an odd integer (von Staudt-Clausen, Fermat).
* `m_tangentNum`: m T_m = (-1)^(m+1) 4^(m-1) g with g odd.
* `secNum_rec`, `secNum_odd`: Σ_k (-1)^(n-k) C(2n,2k) E_k = 0 (from sec cos = 1), hence every
  E_n is an odd integer (Σ_{k<n} C(2n,2k) = 2^(2n-1) - 1 is odd).
* `A223925_main`: the denominator of 4n T_n / E_n divides E_n, so it is odd, and the numerator is
  4^n times an odd number.
Outside Lean: none (only reading the definitions as A000111 and A132049).
-/

open PowerSeries Finset
open scoped Nat

noncomputable section

/-- `sec = 1/cos`, `tan = sin · sec` over ℚ (as in OEIS/A117414/A117414_mathlib.lean). -/
def sec : ℚ⟦X⟧ := (cos ℚ)⁻¹
def tan : ℚ⟦X⟧ := sin ℚ * sec

/-- `D(x) = B(4x) - B(2x) + x` with `B` the e.g.f. of the Bernoulli numbers; `D = x tanh x`. -/
def Dser : ℚ⟦X⟧ :=
  rescale 4 (bernoulliPowerSeries ℚ) - rescale 2 (bernoulliPowerSeries ℚ) + X

lemma cos0 : constantCoeff (cos ℚ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [cos]

lemma tan_mul_cos : tan * cos ℚ = sin ℚ := by
  rw [tan, sec, mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [cos0]; norm_num), mul_one]

lemma exp2_ne : rescale (2 : ℚ) (exp ℚ) - 1 ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp [coeff_rescale] at this

/-- `D · (e^{2x} + 1) = x (e^{2x} - 1)`. -/
lemma Dser_spec : Dser * (rescale (2 : ℚ) (exp ℚ) + 1) = X * (rescale (2 : ℚ) (exp ℚ) - 1) := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h2 : rescale (2 : ℚ) (bernoulliPowerSeries ℚ) * (rescale (2 : ℚ) (exp ℚ) - 1)
      = C (2 : ℚ) * X := by
    rw [← rescale_X, ← hB, map_mul, map_sub, map_one]
  have h4 : rescale (4 : ℚ) (bernoulliPowerSeries ℚ) * (rescale (4 : ℚ) (exp ℚ) - 1)
      = C (4 : ℚ) * X := by
    rw [← rescale_X, ← hB, map_mul, map_sub, map_one]
  have hee : rescale (4 : ℚ) (exp ℚ) = rescale (2 : ℚ) (exp ℚ) * rescale (2 : ℚ) (exp ℚ) := by
    rw [exp_mul_exp_eq_exp_add]; norm_num
  rw [hee] at h4
  have hC2 : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := by rw [map_ofNat]
  have hC4 : (C (4 : ℚ) : ℚ⟦X⟧) = 4 := by rw [map_ofNat]
  rw [hC2] at h2
  rw [hC4] at h4
  apply mul_right_cancel₀ exp2_ne
  unfold Dser
  linear_combination h4 - (rescale (2 : ℚ) (exp ℚ) + 1) * h2

/-! ### Passing to ℂ: `x tan x = -(x tanh x)(i x)`. -/

abbrev toC : ℚ⟦X⟧ →+* ℂ⟦X⟧ := PowerSeries.map (algebraMap ℚ ℂ)

lemma coeff_toC (f : ℚ⟦X⟧) (n : ℕ) : coeff n (toC f) = ((coeff n f : ℚ) : ℂ) := by
  simp [coeff_map]

lemma toC_exp : toC (exp ℚ) = exp ℂ := by
  ext n; simp [coeff_map, exp]

lemma eI : rescale Complex.I (exp ℂ) = toC (cos ℚ) + C Complex.I * toC (sin ℚ) := by
  ext n
  rw [map_add, coeff_C_mul, coeff_rescale, coeff_toC, coeff_toC]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [cos, sin, exp, pow_mul, Complex.I_sq, div_eq_mul_inv]
  · simp [cos, sin, exp, pow_succ, pow_mul, div_eq_mul_inv]
    rw [show (2 * k + 1) / 2 = k by omega]; ring

lemma eI' : rescale (-Complex.I) (exp ℂ) = toC (cos ℚ) - C Complex.I * toC (sin ℚ) := by
  ext n
  rw [map_sub, coeff_C_mul, coeff_rescale, coeff_toC, coeff_toC]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp [cos, sin, exp, pow_mul, Complex.I_sq, div_eq_mul_inv]
  · simp [cos, sin, exp, pow_succ, pow_mul, div_eq_mul_inv]
    rw [show (2 * k + 1) / 2 = k by omega]; ring

lemma eI_mul_eI' : rescale Complex.I (exp ℂ) * rescale (-Complex.I) (exp ℂ) = 1 := by
  rw [exp_mul_exp_eq_exp_add, add_neg_cancel, rescale_zero]
  simp [exp]

lemma toCcos_ne : toC (cos ℚ) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  simp [coeff_map, cos] at this

lemma toC_exp2 : toC (rescale (2 : ℚ) (exp ℚ)) = rescale (2 : ℂ) (exp ℂ) := by
  ext n; simp [coeff_rescale, exp]

lemma rescale_I_exp2 : rescale Complex.I (rescale (2 : ℂ) (exp ℂ))
    = rescale Complex.I (exp ℂ) * rescale Complex.I (exp ℂ) := by
  rw [rescale_rescale, exp_mul_exp_eq_exp_add]; congr 1; ring

/-- Over ℂ: `(x tanh x)(i x) · cos x = -x sin x`. -/
lemma R_mul_cos : rescale Complex.I (toC Dser) * toC (cos ℚ) = -(X * toC (sin ℚ)) := by
  have h := congrArg (fun f => rescale Complex.I (toC f)) Dser_spec
  simp only [map_mul, map_add, map_sub, map_one, map_X, toC_exp2, rescale_I_exp2,
    rescale_X] at h
  have hI : (C Complex.I : ℂ⟦X⟧) * C Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have h1 := eI
  have h2 := eI'
  have h3 := eI_mul_eI'
  set e := rescale Complex.I (exp ℂ)
  set e' := rescale (-Complex.I) (exp ℂ)
  set c := toC (cos ℚ)
  set s := toC (sin ℚ)
  set R := rescale Complex.I (toC Dser)
  have h2ne : (2 : ℂ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [map_ofNat, map_zero] at this
    norm_num at this
  apply mul_left_cancel₀ h2ne
  linear_combination e' * h - (R * e - C Complex.I * X * e) * h3 - R * (h1 + h2)
    + C Complex.I * X * (h1 - h2) + 2 * X * s * hI

lemma R_eq : rescale Complex.I (toC Dser) = -toC (X * tan) := by
  have h : (rescale Complex.I (toC Dser) + toC (X * tan)) * toC (cos ℚ) = 0 := by
    rw [add_mul, R_mul_cos, ← map_mul, mul_assoc, tan_mul_cos, map_mul, map_X]; ring
  have := (mul_eq_zero.mp h).resolve_right toCcos_ne
  linear_combination this

/-- `[x^(2n)] (x tan x) = -(-1)^n [x^(2n)] D`. -/
lemma coeff_Xtan (n : ℕ) : coeff (2 * n) (X * tan) = -(-1) ^ n * coeff (2 * n) Dser := by
  have h := congrArg (coeff (2 * n)) R_eq
  rw [coeff_rescale, map_neg, coeff_toC, coeff_toC, pow_mul, Complex.I_sq] at h
  have : ((coeff (2 * n) (X * tan) : ℚ) : ℂ) = ((-(-1) ^ n * coeff (2 * n) Dser : ℚ) : ℂ) := by
    push_cast; linear_combination h
  exact_mod_cast this

lemma coeff_Dser (n : ℕ) :
    coeff (2 * n) Dser = bernoulli (2 * n) / (2 * n)! * (16 ^ n - 4 ^ n) := by
  have h1 : 2 * n ≠ 1 := by omega
  simp [Dser, coeff_rescale, bernoulliPowerSeries, coeff_X, h1]
  rw [pow_mul, pow_mul]; norm_num; ring

/-- Tangent numbers `T_m = (2m-1)! [x^(2m-1)] tan` (A000182, = A000111(2m-1)). -/
def tangentNum (m : ℕ) : ℚ := (2 * m - 1)! * coeff (2 * m - 1) tan

/-- `T_m = (-1)^(m+1) B_{2m} (16^m - 4^m) / (2m)` for `m ≥ 1`. -/
theorem tangentNum_eq (m : ℕ) (hm : 0 < m) :
    tangentNum m = -(-1) ^ m * bernoulli (2 * m) * (16 ^ m - 4 ^ m) / (2 * m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hX : coeff (2 * n + 1) tan = coeff (2 * (n + 1)) (X * tan) := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, coeff_succ_X_mul]
  rw [tangentNum, e1, hX, coeff_Xtan, coeff_Dser]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1)]
  push_cast
  field_simp
  ring

/-- The denominator of `B_{2m}` divides `2 (4^m - 1)` (von Staudt-Clausen and Fermat). -/
lemma den_dvd (m : ℕ) (hm : 0 < m) : (bernoulli (2 * m)).den ∣ 2 * (4 ^ m - 1) := by
  rw [OpenProblemsLib.BernoulliDen.bernoulli_den_eq_prod m hm]
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Finset.mem_filter.1 hp).2.1.prime
  · intro p hp
    obtain ⟨-, hpp, hpd⟩ := Finset.mem_filter.1 hp
    rcases hpp.eq_two_or_odd' with rfl | hodd
    · exact dvd_mul_right 2 _
    · apply Dvd.dvd.mul_left
      have : Fact p.Prime := ⟨hpp⟩
      have h2 : (2 : ZMod p) ≠ 0 := by
        intro h
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by norm_num) this
        have := hpp.two_le
        obtain ⟨k, hk⟩ := hodd
        omega
      have hf := ZMod.pow_card_sub_one_eq_one h2
      obtain ⟨j, hj⟩ := hpd
      have h4 : (4 : ZMod p) ^ m = 1 := by
        rw [show (4 : ZMod p) = 2 ^ 2 by norm_num, ← pow_mul, hj, pow_mul, hf, one_pow]
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      push_cast; rw [h4, sub_self]

/-- Genocchi numbers: `2 (4^m - 1) B_{2m}` is an odd integer for `m ≥ 1`. -/
theorem genocchi_odd (m : ℕ) (hm : 0 < m) :
    ∃ g : ℤ, Odd g ∧ 2 * (4 ^ m - 1) * bernoulli (2 * m) = g := by
  obtain ⟨Q, hQ⟩ := den_dvd m hm
  set D := (bernoulli (2 * m)).den
  set N := (bernoulli (2 * m)).num
  have hD4 := OpenProblemsLib.BernoulliDen.bernoulli_den_mod4 m hm
  refine ⟨N * Q, ?_, ?_⟩
  · apply Int.odd_mul.mpr
    constructor
    · have hcop := (bernoulli (2 * m)).reduced
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      have h2D : 2 ∣ D := by omega
      have := Nat.Coprime.coprime_dvd_left (show 2 ∣ N.natAbs by
        rw [← Int.natCast_dvd]; simpa using h2) hcop
      have := Nat.Coprime.coprime_dvd_right h2D this
      norm_num at this
    · rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      have h2' : 2 ∣ Q := by exact_mod_cast h2
      have h4 : 4 ∣ 2 * (4 ^ m - 1) := by
        rw [hQ]; obtain ⟨a, ha⟩ := h2'; rw [ha]
        have : 2 ∣ D := by omega
        obtain ⟨b, hb⟩ := this; rw [hb]; exact ⟨b * a, by ring⟩
      have hodd : (4 ^ m - 1) % 2 = 1 := by
        have : 4 ^ m % 2 = 0 := by
          rw [Nat.pow_mod]; norm_num; rw [Nat.zero_pow hm]
        have : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
        omega
      omega
  · have hB : bernoulli (2 * m) = (N : ℚ) / D := (Rat.num_div_den _).symm
    have hDpos : (D : ℚ) ≠ 0 := by exact_mod_cast (bernoulli (2 * m)).den_nz
    have hQ' : (2 * (4 ^ m - 1 : ℕ) : ℚ) = (D : ℚ) * Q := by exact_mod_cast hQ
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))] at hQ'
    push_cast at hQ' ⊢
    rw [hB]
    field_simp
    linear_combination (N : ℚ) * hQ'

/-- 2-adic valuation of the tangent numbers: `m T_m = ± 4^(m-1) g` with `g` odd. -/
theorem m_tangentNum (m : ℕ) (hm : 0 < m) :
    ∃ g : ℤ, Odd g ∧ m * tangentNum m = (-1) ^ (m + 1) * 4 ^ (m - 1) * g := by
  obtain ⟨g, hg, hgB⟩ := genocchi_odd m hm
  refine ⟨g, hg, ?_⟩
  rw [tangentNum_eq m hm, ← hgB]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h16 : (16 : ℚ) ^ (n + 1) = 4 ^ (n + 1) * 4 ^ (n + 1) := by rw [← mul_pow]; norm_num
  rw [h16]
  have : (n + 1 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### Step 1: the secant numbers are odd integers -/

/-- `Bh n = (2n)!/2^n`. -/
def Bh (n : ℕ) : ℚ := ((2 * n)! : ℚ) / 2 ^ n

lemma Bh_ne (n : ℕ) : Bh n ≠ 0 := by unfold Bh; positivity

/-- `E(-z) = Σ (-1)^n z^n / Bh n`, so that `cos x = E(-x^2/2)`. -/
def Em : ℚ⟦X⟧ := mk fun n => (-1) ^ n / Bh n

lemma Em0 : constantCoeff Em = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Em, coeff_mk]; simp [Bh]

def Einv : ℚ⟦X⟧ := Em⁻¹

def phi : ℚ⟦X⟧ →+* ℚ⟦X⟧ :=
  (expand 2 two_ne_zero : ℚ⟦X⟧ →ₐ[ℚ] ℚ⟦X⟧).toRingHom.comp (rescale (1 / 2 : ℚ))

lemma phi_even (f : ℚ⟦X⟧) (n : ℕ) : coeff (2 * n) (phi f) = coeff n f / 2 ^ n := by
  simp [phi, coeff_rescale, div_eq_inv_mul]

lemma phi_odd (f : ℚ⟦X⟧) (n : ℕ) : coeff (2 * n + 1) (phi f) = 0 := by
  simp only [phi, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  exact coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega)

lemma phi_Em : phi Em = cos ℚ := by
  ext i
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [phi_even, Em, coeff_mk, Bh]
    simp [cos]
    field_simp
  · rw [phi_odd]; simp [cos]

lemma phi_Einv : phi Einv = sec := by
  have h : phi Einv * cos ℚ = 1 := by
    rw [← phi_Em, ← map_mul, Einv, PowerSeries.inv_mul_cancel _ (by rw [Em0]; norm_num),
      map_one]
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by rw [cos0]; norm_num)).2 h

/-- Secant (Euler) numbers `E_n = (2n)! [x^(2n)] sec` (A000364(n) = A000111(2n)). -/
def secNum (n : ℕ) : ℚ := (2 * n)! * coeff (2 * n) sec

lemma secNum_eq (n : ℕ) : secNum n = Bh n * coeff n Einv := by
  rw [secNum, ← phi_Einv, phi_even, Bh]; field_simp

lemma Bh_div (n k : ℕ) (hk : k ≤ n) : Bh n / (Bh k * Bh (n - k)) = ((2 * n).choose (2 * k) : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * n by omega)
  have e : 2 * n - 2 * k = 2 * (n - k) := by omega
  rw [e] at h
  have hq : ((2 * n).choose (2 * k) : ℚ) * (2 * k)! * (2 * (n - k))! = (2 * n)! := by exact_mod_cast h
  unfold Bh
  have h2 : (2 : ℚ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [h2, ← hq]
  field_simp

/-- Recurrence from `Einv · Em = 1`: `Σ_{k ≤ n} (-1)^(n-k) C(2n, 2k) E_k = 0` for `n ≥ 1`. -/
lemma secNum_rec (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range (n + 1), (-1) ^ (n - k) * ((2 * n).choose (2 * k) : ℚ) * secNum k = 0 := by
  have h := congrArg (coeff n) (PowerSeries.inv_mul_cancel Em (by rw [Em0]; norm_num))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_one] at h
  simp only [show n ≠ 0 by omega, ↓reduceIte] at h
  rw [← mul_zero (Bh n), ← h, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by rw [mem_range] at hk; omega
  rw [secNum_eq, ← Bh_div n k hk']
  unfold Einv
  rw [show coeff (n - k) Em = (-1) ^ (n - k) / Bh (n - k) by rw [Em, coeff_mk]]
  have := Bh_ne k
  have := Bh_ne (n - k)
  have := Bh_ne n
  field_simp

lemma sum_choose_even_aux (N : ℕ) : ∀ m, ∑ i ∈ range (m + 1), (N + 1).choose (2 * i)
    = ∑ j ∈ range (2 * m + 1), N.choose j
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, sum_choose_even_aux N m]
    have e1 : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
    have e2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [e1, e2, sum_range_succ, sum_range_succ, Nat.choose_succ_succ, add_assoc]
    rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring]
    simp only [sum_range_succ, Nat.succ_eq_add_one]
    ring

/-- `Σ_{k < n} C(2n, 2k) = 2^(2n-1) - 1` for `n ≥ 1`. -/
lemma sum_choose_even_lt (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (2 * n).choose (2 * k) + 1 = 2 ^ (2 * n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := sum_choose_even_aux (2 * k + 1) (k + 1)
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, sum_range_succ, Nat.choose_self] at h
  rw [h, show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 by ring, sum_range_succ,
    Nat.choose_succ_self, add_zero, Nat.sum_range_choose]
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]

lemma even_sum_of (s : Finset ℕ) (f : ℕ → ℤ) (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Step 1: every secant number is an odd integer. -/
theorem secNum_odd (n : ℕ) : ∃ z : ℤ, Odd z ∧ secNum n = z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, odd_one, ?_⟩
    rw [secNum_eq, Einv, coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, Em0]
    simp [Bh]
  choose! Z hZo hZ using ih
  have hrec := secNum_rec n hn
  rw [sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self] at hrec
  refine ⟨-∑ k ∈ range n, (-1) ^ (n - k) * ((2 * n).choose (2 * k) : ℤ) * Z k, ?_, ?_⟩
  · have hS := sum_choose_even_lt n hn
    have hev : Even ((-∑ k ∈ range n, (-1) ^ (n - k) * ((2 * n).choose (2 * k) : ℤ) * Z k)
        + ∑ k ∈ range n, ((2 * n).choose (2 * k) : ℤ)) := by
      rw [neg_add_eq_sub, ← sum_sub_distrib]
      apply even_sum_of
      intro k hk
      have hzk := hZo k (mem_range.mp hk)
      have ho : Odd ((-1) ^ (n - k) * Z k) := ((Int.odd_iff.mpr (by norm_num) : Odd (-1 : ℤ)).pow).mul hzk
      have : ((2 * n).choose (2 * k) : ℤ) - (-1) ^ (n - k) * ((2 * n).choose (2 * k) : ℤ) * Z k
          = ((2 * n).choose (2 * k) : ℤ) * (1 - (-1) ^ (n - k) * Z k) := by ring
      rw [this]
      exact (odd_one.sub_odd ho).mul_left _
    have hSo : Odd (∑ k ∈ range n, ((2 * n).choose (2 * k) : ℤ)) := by
      have : (∑ k ∈ range n, ((2 * n).choose (2 * k) : ℤ)) = ((2 ^ (2 * n - 1) - 1 : ℕ) : ℤ) := by
        rw [← hS]; push_cast; simp
      rw [this]
      have h2 : Even (2 ^ (2 * n - 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have h1 : 1 ≤ 2 ^ (2 * n - 1) := Nat.one_le_two_pow
      exact_mod_cast Nat.Even.sub_odd h1 h2 odd_one
    have := hev.sub_odd hSo
    rw [add_sub_cancel_right] at this
    exact this
  · push_cast
    have e : secNum n = -∑ k ∈ range n, (-1) ^ (n - k) * ((2 * n).choose (2 * k) : ℚ) * secNum k := by
      simp at hrec; linarith
    rw [e]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [hZ k (mem_range.mp hk)]

/-! ### Step 3: the reduced numerator -/

/-- `A132049(2n)`: numerator of `2 (2n) A000111(2n-1) / A000111(2n) = 4n T_n / E_n` in lowest terms. -/
def A132049_even (n : ℕ) : ℤ := (((2 * (2 * n) : ℕ) : ℚ) * tangentNum n / secNum n).num

lemma isCoprime_two_pow_of_odd {e : ℤ} (he : Odd e) (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) e := by
  apply IsCoprime.pow_left
  obtain ⟨j, rfl⟩ := he
  exact ⟨-j, 1, by ring⟩

/-- Main theorem: for every `n ≥ 1`, `A132049(2n) = 4^n · u` with `u` odd. In particular
`a(2n) = 4^n` divides `A132049(2n)` (the conjecture), and `4^n` is the exact power of 2. -/
theorem A223925_main (n : ℕ) (hn : 0 < n) :
    ∃ u : ℤ, Odd u ∧ A132049_even n = 4 ^ n * u := by
  obtain ⟨g, hg, hT⟩ := m_tangentNum n hn
  obtain ⟨e, he, hE⟩ := secNum_odd n
  have he0 : (e : ℚ) ≠ 0 := by
    have : e ≠ 0 := by rintro rfl; exact (Int.not_even_iff_odd.mpr he) ⟨0, rfl⟩
    exact_mod_cast this
  set a : ℤ := (-1) ^ (n + 1) * 4 ^ n * g with ha
  set q : ℚ := ((2 * (2 * n) : ℕ) : ℚ) * tangentNum n / secNum n with hq
  have hqa : q = (a : ℚ) / e := by
    rw [hq, hE, ha]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hT
    push_cast at hT ⊢
    rw [show (2 * (2 * ((k : ℚ) + 1))) * tangentNum (k + 1)
        = 4 * (((k : ℚ) + 1) * tangentNum (k + 1)) by ring, hT]
    ring
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have key : q.num * e = a * q.den := by
    have h1 : (q.num : ℚ) / q.den = a / e := by rw [Rat.num_div_den, hqa]
    rw [div_eq_div_iff hden he0] at h1
    exact_mod_cast h1
  -- the denominator is odd
  have hcop : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := q.reduced
    rw [Int.gcd_comm]; simpa [Int.gcd] using this
  have hdd : (q.den : ℤ) ∣ e := by
    apply hcop.dvd_of_dvd_mul_left
    exact ⟨a, by rw [key]; ring⟩
  have hdodd : Odd (q.den : ℤ) := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    exact (Int.not_even_iff_odd.mpr he) (even_iff_two_dvd.mpr (h2.trans hdd))
  -- 4^n divides the numerator
  have h4 : (4 : ℤ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hc4 : IsCoprime ((4 : ℤ) ^ n) e := by rw [h4]; exact isCoprime_two_pow_of_odd he _
  have hdiv : (4 : ℤ) ^ n ∣ q.num := by
    apply hc4.dvd_of_dvd_mul_right
    exact ⟨(-1) ^ (n + 1) * g * q.den, by rw [key, ha]; ring⟩
  obtain ⟨u, hu⟩ := hdiv
  refine ⟨u, ?_, by rw [A132049_even, ← hq, hu]⟩
  have h40 : (4 : ℤ) ^ n ≠ 0 := by positivity
  have hue : u * e = (-1) ^ (n + 1) * g * q.den := by
    apply mul_left_cancel₀ h40
    rw [← mul_assoc, ← hu, key, ha]; ring
  have hodd : Odd ((-1) ^ (n + 1) * g * (q.den : ℤ)) :=
    (((Int.odd_iff.mpr (by norm_num) : Odd (-1 : ℤ)).pow).mul hg).mul hdodd
  rw [← hue] at hodd
  exact (Int.odd_mul.mp hodd).1

end
