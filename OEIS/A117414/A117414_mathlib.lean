/-
OEIS A117414, Mathlib proof.

The entry has no definition; Critzer's g.f. is taken as the definition:
  Sum_{n,k} T(n,k) u^k z^n / B(n) = E((u-1)z) / E(-z),
  B(n) = (2n)!/2^n,  E(z) = Sum_n z^n / B(n).
In Lean `G` is this bivariate series in `(Polynomial ℚ)⟦X⟧` (u is the polynomial
variable, z the power-series variable): `G = Gnum * C(E(-z)⁻¹)` with
`Gnum = Sum_m C(1/B m) (u-1)^m z^m`, so `G * C(E(-z)) = Gnum` (`G_spec`), and
`T n k = B n * [u^k] [z^n] G`.

Euler and tangent numbers come from formal power series over ℚ:
`sec = cos⁻¹`, `tan = sin * sec` (Mathlib `PowerSeries.cos`, `PowerSeries.sin`).
  A000364(n) = (2n)! [x^(2n)] sec                     (`euler`)
  A024255(n) = n * (2n-1)! [x^(2n-1)] tan             (`A024255`)
  A117415(n) = (2n)! [x^(2n)] (x tan x - x^2)/8       (`A117415`)

Main theorem `A117414_main`, for every n:
  (1) Sum_{k=0..n} T(n,k) = A000364(n),
  (2) T(n,1) = A024255(n),
  (3) T(n,2) = A117415(n).

Method: the ring map phi = expand 2 ∘ rescale (1/2) (z ↦ x^2/2) sends E(-z) to cos,
hence 1/E(-z) to sec, and sends the u^1, u^2 parts of E((u-1)z) to
x sin(x)/2 and (x sin x - x^2 cos x)/8.

Outside Lean: none (the choice of Critzer's g.f. as the definition is a reading
of the entry, stated in the README).
-/
import Mathlib

open PowerSeries Finset
open scoped Nat

namespace A117414

/-- `B(n) = (2n)!/2^n`. -/
noncomputable def B (n : ℕ) : ℚ := ((2 * n)! : ℚ) / 2 ^ n

lemma B_ne (n : ℕ) : B n ≠ 0 := by unfold B; positivity

/-- `E(-z) = Sum_n (-1)^n z^n / B(n)`. -/
noncomputable def Em : ℚ⟦X⟧ := mk fun n => (-1) ^ n / B n

noncomputable def Einv : ℚ⟦X⟧ := Em⁻¹

/-- `E((u-1)z) = Sum_m (u-1)^m z^m / B(m)`. -/
noncomputable def Gnum : PowerSeries (Polynomial ℚ) :=
  mk fun m => Polynomial.C (1 / B m) * (Polynomial.X - 1) ^ m

/-- Critzer's g.f. `E((u-1)z) / E(-z)`. -/
noncomputable def G : PowerSeries (Polynomial ℚ) := Gnum * map Polynomial.C Einv

/-- The triangle. -/
noncomputable def T (n k : ℕ) : ℚ := B n * (coeff n G).coeff k

noncomputable def sec : ℚ⟦X⟧ := (cos ℚ)⁻¹
noncomputable def tan : ℚ⟦X⟧ := sin ℚ * sec

/-- Euler (secant) numbers A000364. -/
noncomputable def euler (n : ℕ) : ℚ := (2 * n)! * coeff (2 * n) sec

/-- A024255(n) = n t(2n-1), t the tangent numbers. -/
noncomputable def A024255 (n : ℕ) : ℚ := n * ((2 * n - 1)! * coeff (2 * n - 1) tan)

/-- A117415: e.g.f. (x tan x - x^2)/8, even powers. -/
noncomputable def A117415 (n : ℕ) : ℚ :=
  (2 * n)! * coeff (2 * n) (C (1 / 8 : ℚ) * (X * tan - X ^ 2))

lemma Em0 : constantCoeff Em = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Em, coeff_mk]; simp [B]

/-- `G` is `E((u-1)z)` divided by `E(-z)`. -/
lemma G_spec : G * map Polynomial.C Em = Gnum := by
  rw [G, mul_assoc, ← map_mul, Einv,
    PowerSeries.inv_mul_cancel _ (by rw [Em0]; norm_num), map_one, mul_one]

/-- The `u^k` part of `E((u-1)z)`. -/
noncomputable def Nk (k : ℕ) : ℚ⟦X⟧ := mk fun m => (coeff m Gnum).coeff k

lemma coeff_Nk (k m : ℕ) : coeff m (Nk k) = 1 / B m * ((-1) ^ (m - k) * (m.choose k : ℚ)) := by
  rw [Nk, coeff_mk, Gnum, coeff_mk, Polynomial.coeff_C_mul]
  congr 1
  rw [sub_eq_add_neg, ← Polynomial.C_1, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]

lemma T_eq (n k : ℕ) : T n k = B n * coeff n (Nk k * Einv) := by
  rw [T, G, coeff_mul, coeff_mul, Polynomial.finsetSum_coeff]
  congr 1
  apply sum_congr rfl
  intro x _
  simp [Nk, Polynomial.coeff_mul_C]

/-! ### The substitution z ↦ x^2/2 -/

noncomputable def phi : ℚ⟦X⟧ →+* ℚ⟦X⟧ :=
  (expand 2 two_ne_zero : ℚ⟦X⟧ →ₐ[ℚ] ℚ⟦X⟧).toRingHom.comp (rescale (1 / 2 : ℚ))

lemma phi_even (f : ℚ⟦X⟧) (n : ℕ) : coeff (2 * n) (phi f) = coeff n f / 2 ^ n := by
  simp [phi, coeff_rescale, div_eq_inv_mul]

lemma phi_odd (f : ℚ⟦X⟧) (n : ℕ) : coeff (2 * n + 1) (phi f) = 0 := by
  simp only [phi, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  exact coeff_expand_of_not_dvd 2 two_ne_zero _ (by omega)

lemma coeff_cos_even (n : ℕ) : coeff (2 * n) (cos ℚ) = (-1) ^ n / (2 * n)! := by
  simp [cos]

lemma coeff_cos_odd (n : ℕ) : coeff (2 * n + 1) (cos ℚ) = 0 := by
  simp [cos]

lemma coeff_sin_even (n : ℕ) : coeff (2 * n) (sin ℚ) = 0 := by
  simp [sin]

lemma coeff_sin_odd (n : ℕ) : coeff (2 * n + 1) (sin ℚ) = (-1) ^ n / (2 * n + 1)! := by
  simp [sin]
  congr 2
  omega

lemma phi_Em : phi Em = cos ℚ := by
  ext i
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [phi_even, coeff_cos_even, Em, coeff_mk, B]
    field_simp
  · rw [phi_odd, coeff_cos_odd]

lemma cos0 : constantCoeff (cos ℚ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simpa using coeff_cos_even 0

lemma phi_Einv : phi Einv = sec := by
  have h : phi Einv * cos ℚ = 1 := by
    rw [← phi_Em, ← map_mul, Einv, PowerSeries.inv_mul_cancel _ (by rw [Em0]; norm_num),
      map_one]
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by rw [cos0]; norm_num)).2 h

/-- Coefficient `n` of `f * Einv` read off as coefficient `2n` after `phi`. -/
lemma coeff_via_phi (f : ℚ⟦X⟧) (n : ℕ) :
    B n * coeff n (f * Einv) = (2 * n)! * coeff (2 * n) (phi f * sec) := by
  rw [← phi_Einv, ← map_mul, phi_even, B]
  field_simp

/-! ### Row sums -/

lemma rowsum_coeff (n m : ℕ) (hm : m ≤ n) :
    ∑ k ∈ range (n + 1), coeff m (Nk k) = if m = 0 then 1 else 0 := by
  simp only [coeff_Nk, ← Finset.mul_sum]
  have h1 : ∑ k ∈ range (n + 1), ((-1 : ℚ) ^ (m - k) * (m.choose k : ℚ)) =
      ∑ k ∈ range (m + 1), ((1 : ℚ) ^ k * (-1) ^ (m - k) * (m.choose k : ℚ)) := by
    symm
    apply Finset.sum_subset_zero_on_sdiff (range_subset_range.2 (by omega))
    · intro k hk
      simp only [mem_sdiff, mem_range] at hk
      simp [Nat.choose_eq_zero_of_lt (show m < k by omega)]
    · intro k _; simp
  rw [h1, ← add_pow]
  rcases m with _ | m
  · simp [B]
  · simp

theorem rowsum (n : ℕ) : ∑ k ∈ range (n + 1), T n k = euler n := by
  simp only [T_eq, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]
  rw [euler, ← phi_Einv, phi_even, B]
  have h : coeff n ((∑ k ∈ range (n + 1), Nk k) * Einv) = coeff n Einv := by
    rw [coeff_mul, ← one_mul Einv, coeff_mul, one_mul]
    apply sum_congr rfl
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_sum, rowsum_coeff n x.1 (by omega), coeff_one]
  rw [h]
  field_simp

/-! ### Column 1 -/

lemma phi_N1 : phi (Nk 1) = C (1 / 2 : ℚ) * (X * sin ℚ) := by
  ext i
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [phi_even, coeff_Nk, coeff_C_mul]
    rcases n with _ | n
    · simp
    · rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, coeff_succ_X_mul, coeff_sin_odd, B]
      simp only [Nat.choose_one_right, show n + 1 - 1 = n by omega]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      field_simp
      ring
  · rw [phi_odd, coeff_C_mul, coeff_succ_X_mul, coeff_sin_even, mul_zero]

theorem col1 (n : ℕ) : T n 1 = A024255 n := by
  have h : C (1 / 2 : ℚ) * (X * sin ℚ) * sec = C (1 / 2 : ℚ) * (X * tan) := by
    rw [tan]; ring
  rw [T_eq, coeff_via_phi, phi_N1, h, A024255, coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      show 2 * (n + 1) = (2 * n + 1) + 1 by ring, coeff_succ_X_mul, Nat.factorial_succ]
    push_cast
    ring

/-! ### Column 2 -/

lemma coeff_sin_odd' (n : ℕ) : coeff (2 * n + 3) (sin ℚ) = (-1) ^ (n + 1) / (2 * n + 3)! := by
  have h := coeff_sin_odd (n + 1)
  rwa [show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at h

lemma phi_N2 : phi (Nk 2) = C (1 / 8 : ℚ) * (X * sin ℚ - X ^ 2 * cos ℚ) := by
  ext i
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [phi_even, coeff_Nk, coeff_C_mul, map_sub]
    rcases n with _ | _ | n
    · simp
    · have h1 := coeff_sin_odd 0
      simp at h1
      simp [coeff_X_pow_mul', coeff_succ_X_mul, h1, cos0]
    · rw [show 2 * (n + 2) = (2 * n + 3) + 1 by ring, coeff_succ_X_mul, coeff_sin_odd' n,
        coeff_X_pow_mul']
      simp only [show 2 ≤ 2 * n + 3 + 1 by omega, ↓reduceIte]
      rw [show 2 * n + 3 + 1 - 2 = 2 * (n + 1) by omega, coeff_cos_even, B, Nat.cast_choose_two,
        show n + 2 - 2 = n by omega, show 2 * n + 3 = 2 * (n + 1) + 1 by ring,
        show 2 * (n + 2) = 2 * (n + 1) + 1 + 1 by ring, Nat.factorial_succ (2 * (n + 1) + 1),
        Nat.factorial_succ (2 * (n + 1))]
      push_cast
      field_simp
      ring
  · rw [phi_odd, coeff_C_mul, map_sub, coeff_succ_X_mul, coeff_sin_even, coeff_X_pow_mul']
    split_ifs with h
    · rw [show 2 * n + 1 - 2 = 2 * (n - 1) + 1 by omega, coeff_cos_odd]; simp
    · simp

theorem col2 (n : ℕ) : T n 2 = A117415 n := by
  have hcs : cos ℚ * sec = 1 := PowerSeries.mul_inv_cancel _ (by rw [cos0]; norm_num)
  have h : C (1 / 8 : ℚ) * (X * sin ℚ - X ^ 2 * cos ℚ) * sec =
      C (1 / 8 : ℚ) * (X * tan - X ^ 2) := by
    calc C (1 / 8 : ℚ) * (X * sin ℚ - X ^ 2 * cos ℚ) * sec
        = C (1 / 8 : ℚ) * (X * (sin ℚ * sec) - X ^ 2 * (cos ℚ * sec)) := by ring
      _ = C (1 / 8 : ℚ) * (X * tan - X ^ 2) := by rw [hcs, tan]; ring
  rw [T_eq, coeff_via_phi, phi_N2, h, A117415]

theorem A117414_main (n : ℕ) :
    ∑ k ∈ range (n + 1), T n k = euler n ∧ T n 1 = A024255 n ∧ T n 2 = A117415 n :=
  ⟨rowsum n, col1 n, col2 n⟩
