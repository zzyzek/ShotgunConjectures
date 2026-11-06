import Mathlib

/-
OEIS A212425 and A212392 (P. D. Hanna, 2012): the power series A(x) with
A(x) = (x + A(A(x)))^b, for b = 3 (A212425, A(x) = sum a(n) x^(8n-5)) and
b = 2 (A212392, A(x) = sum a(n) x^(3n-1)).  Conjectures: (2n-1) | a(n)
for b = 3, n | a(n) for b = 2, and in general, with
A(x) = sum a(n) x^((b^2-1)(n-1)+b), ((b-1)(n-1)+1) | a(n).

Main theorems (any b ≥ 2, any F ∈ ℤ⟦X⟧ with constant coefficient 0 and
F = (X + F∘F)^b):
* `A212425_dvd_all`: (k+1) ∣ (b+1) · [x^k] F for every k.
* `A212425_main`: ((b-1)(n-1)+1) ∣ [x^((b^2-1)(n-1)+b)] F for n ≥ 1, the
  general conjecture; `A212425_b3`, `A212392_b2` are b = 3 and b = 2.

Route.  Over ℚ let J be the antiderivative of (b+1) F and u = X + F∘F, so
u^b = F.  Differentiating (chain rule `derivative_subst`) shows
  J - J∘F = u^(b+1) - (b+1) F (F∘F)          (`A212425_identity`)
(both sides have derivative (b+1)(F - F'·(F∘F)) and vanish at 0).  The
right side has integer coefficients and X^2 ∣ F, so the coefficient of x^n
in J∘F only involves coefficients of J of degree < n; by strong induction
every coefficient of J is an integer (`A212425_integral`).  The coefficient
of x^(k+1) in J is (b+1)[x^k]F/(k+1).

Not checked here: that the OEIS g.f. exists (Abbondandolo-Majer,
arXiv:2610.33287, Lemma 7.1: the equation has a unique solution in
x·ℝ[[x]], with integer coefficients) -- the theorems hold for every solution.
-/

open PowerSeries

/-- Integers inside ℚ. -/
abbrev A212425_S : Subring ℚ := (Int.castRingHom ℚ).range

theorem A212425_zero_of_derivative (D : ℚ⟦X⟧) (h0 : constantCoeff D = 0)
    (hd : d⁄dX D = 0) : D = 0 := by
  ext n
  cases n with
  | zero => simpa using h0
  | succ n =>
    have := congrArg (coeff n) hd
    rw [coeff_derivative, map_zero] at this
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    simpa [hn] using this

/-- Integrality: if X^2 ∣ G, J(0) = 0 and J - J∘G has integer coefficients,
so does J. -/
theorem A212425_integral (G H : ℤ⟦X⟧) (hG : G.map (Int.castRingHom ℚ) = X ^ 2 * H.map (Int.castRingHom ℚ))
    (J R : ℚ⟦X⟧) (hJ0 : constantCoeff J = 0)
    (hR : ∀ n, coeff n R ∈ A212425_S)
    (hJ : J - J.subst (G.map (Int.castRingHom ℚ)) = R) :
    ∀ n, coeff n J ∈ A212425_S := by
  set Gq := G.map (Int.castRingHom ℚ) with hGq
  have hsub : HasSubst Gq := HasSubst.of_constantCoeff_zero' (by
    rw [hG]; simp)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, hJ0]; exact Subring.zero_mem _
    · have e : coeff (n + 1) J = coeff (n + 1) R + coeff (n + 1) (J.subst Gq) := by
        rw [← hJ]; simp
      rw [e]
      refine Subring.add_mem _ (hR _) ?_
      rw [coeff_subst' hsub]
      have hpow : ∀ d, coeff (n + 1) (Gq ^ d) =
          if 2 * d ≤ n + 1 then coeff (n + 1 - 2 * d) (H.map (Int.castRingHom ℚ) ^ d) else 0 := by
        intro d
        rw [hG, mul_pow, ← pow_mul, coeff_X_pow_mul']
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
      · refine Subring.sum_mem _ fun d hd => ?_
        rw [smul_eq_mul]
        refine Subring.mul_mem _ (ih d (Finset.mem_range.mp hd)) ?_
        rw [hGq, ← map_pow, coeff_map]
        exact ⟨_, rfl⟩
      · intro d hd
        rw [Function.mem_support] at hd
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hc
        apply hd
        rw [hpow d]
        simp only [show ¬ (2 * d ≤ n + 1) by omega, ↓reduceIte, smul_zero]

/-- Antiderivative of (b+1) F. -/
noncomputable def A212425_J (b : ℕ) (F : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  mk fun k => if k = 0 then 0 else ((b : ℚ) + 1) * coeff (k - 1) F / k

theorem A212425_J_deriv (b : ℕ) (F : ℚ⟦X⟧) : d⁄dX (A212425_J b F) = ((b : ℚ⟦X⟧) + 1) * F := by
  ext n
  rw [coeff_derivative]
  simp only [A212425_J, coeff_mk, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have : ((b : ℚ⟦X⟧) + 1) = C ((b : ℚ) + 1) := by simp
  rw [this, coeff_C_mul]
  push_cast
  field_simp

theorem A212425_identity (b : ℕ) (F : ℚ⟦X⟧) (h0 : constantCoeff F = 0)
    (hF : F = (X + F.subst F) ^ b) :
    A212425_J b F - (A212425_J b F).subst F =
      (X + F.subst F) ^ (b + 1) - ((b : ℚ⟦X⟧) + 1) * (F * F.subst F) := by
  have hs : HasSubst F := HasSubst.of_constantCoeff_zero' h0
  rw [← sub_eq_zero]
  apply A212425_zero_of_derivative
  · have h1 : constantCoeff (A212425_J b F) = 0 := by
      simp [A212425_J, ← coeff_zero_eq_constantCoeff_apply]
    have h2 : constantCoeff ((A212425_J b F).subst F) = 0 := by
      exact constantCoeff_subst_eq_zero (R := ℚ) (S := ℚ) h0 (A212425_J b F) h1
    have h3 : constantCoeff (F.subst F) = 0 := by
      exact constantCoeff_subst_eq_zero (R := ℚ) (S := ℚ) h0 F h0
    simp [h1, h2, h3, h0]
  · set u := X + F.subst F with hu
    have hdu : d⁄dX u = 1 + (d⁄dX F).subst F * d⁄dX F := by
      rw [hu, map_add, derivative_X, derivative_subst hs]
    have hJs : d⁄dX ((A212425_J b F).subst F) = ((b : ℚ⟦X⟧) + 1) * F.subst F * d⁄dX F := by
      rw [derivative_subst hs, A212425_J_deriv, ← coe_substAlgHom hs, map_mul, map_add, map_one,
        map_natCast]
    have hFF : d⁄dX (F * F.subst F) = F * ((d⁄dX F).subst F * d⁄dX F) + F.subst F * d⁄dX F := by
      rw [Derivation.leibniz, derivative_subst hs, smul_eq_mul, smul_eq_mul]
    have hup : d⁄dX (u ^ (b + 1)) = ((b : ℚ⟦X⟧) + 1) * F * d⁄dX u := by
      rw [Derivation.leibniz_pow, Nat.add_sub_cancel, ← hF, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    have hc : d⁄dX ((b : ℚ⟦X⟧) + 1) = 0 := by
      rw [map_add, Derivation.map_natCast, Derivation.map_one_eq_zero, add_zero]
    rw [map_sub, map_sub, map_sub, hJs, A212425_J_deriv, hup, Derivation.leibniz, hFF, hc, hdu,
      smul_eq_mul, smul_eq_mul]
    ring

theorem A212425_dvd_all (b : ℕ) (hb : 2 ≤ b) (F : ℤ⟦X⟧) (h0 : constantCoeff F = 0)
    (hF : F = (X + F.subst F) ^ b) (k : ℕ) :
    ((k : ℤ) + 1) ∣ ((b : ℤ) + 1) * coeff k F := by
  set φ := Int.castRingHom ℚ
  have hs : HasSubst F := HasSubst.of_constantCoeff_zero' h0
  set Fq := F.map φ with hFq_def
  have h0q : constantCoeff Fq = 0 := by
    rw [hFq_def, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      h0, map_zero]
  have hms : ∀ f : ℤ⟦X⟧, PowerSeries.map φ (f.subst F) =
      (PowerSeries.map φ f).subst (PowerSeries.map φ F) := fun f => map_subst hs f
  have hFq : Fq = (X + Fq.subst Fq) ^ b := by
    conv_lhs => rw [hFq_def, hF]
    rw [map_pow, map_add, map_X, hms]
  -- X^2 divides F
  have hu0 : constantCoeff (X + F.subst F) = 0 := by
    have : constantCoeff (F.subst F) = 0 := constantCoeff_subst_eq_zero (R := ℤ) (S := ℤ) h0 F h0
    simp [this]
  obtain ⟨v, hv⟩ := (X_dvd_iff).mpr hu0
  set H := X ^ (b - 2) * v ^ b
  have hFH : F = X ^ 2 * H := by
    rw [hF, hv, mul_pow]
    have : X ^ b = (X : ℤ⟦X⟧) ^ 2 * X ^ (b - 2) := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have hG : Fq = X ^ 2 * H.map φ := by
    rw [hFq_def, hFH, map_mul, map_pow, map_X]
  have hid := A212425_identity b Fq h0q hFq
  set R := (X + Fq.subst Fq) ^ (b + 1) - ((b : ℚ⟦X⟧) + 1) * (Fq * Fq.subst Fq)
  have hR : R = ((X + F.subst F) ^ (b + 1) - ((b : ℤ⟦X⟧) + 1) * (F * F.subst F)).map φ := by
    simp only [R, map_sub, map_pow, map_add, map_X, map_mul, hms, map_natCast, map_one, Fq]
  have hRint : ∀ n, coeff n R ∈ A212425_S := by
    intro n; rw [hR, coeff_map]; exact ⟨_, rfl⟩
  have hJ0 : constantCoeff (A212425_J b Fq) = 0 := by
    simp [A212425_J, ← coeff_zero_eq_constantCoeff_apply]
  have hint := A212425_integral F H hG (A212425_J b Fq) R hJ0 hRint hid (k + 1)
  obtain ⟨z, hz⟩ := hint
  simp only [A212425_J, coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hz
  rw [hFq_def, coeff_map] at hz
  refine ⟨z, ?_⟩
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have : (((b : ℤ) + 1) * coeff k F : ℚ) = ((z * ((k : ℤ) + 1) : ℤ) : ℚ) := by
    rw [show φ (coeff k F) = ((coeff k F : ℤ) : ℚ) from rfl] at hz
    have hz' : (z : ℚ) = ((b : ℚ) + 1) * ((coeff k F : ℤ) : ℚ) / ((k : ℚ) + 1) := by
      have h2 := hz
      simp only [eq_intCast] at h2
      rw [h2]; push_cast; ring
    push_cast
    rw [hz']
    field_simp
  have h2 : ((b : ℤ) + 1) * coeff k F = z * ((k : ℤ) + 1) := by exact_mod_cast this
  rw [h2, mul_comm]

/-- The general conjecture of A212425 / A212392: with
A(x) = sum a(n) x^((b^2-1)(n-1)+b), ((b-1)(n-1)+1) ∣ a(n). -/
theorem A212425_main (b : ℕ) (hb : 2 ≤ b) (F : ℤ⟦X⟧) (h0 : constantCoeff F = 0)
    (hF : F = (X + F.subst F) ^ b) (n : ℕ) (hn : 1 ≤ n) :
    (((b - 1) * (n - 1) + 1 : ℕ) : ℤ) ∣ coeff ((b ^ 2 - 1) * (n - 1) + b) F := by
  have h := A212425_dvd_all b hb F h0 hF ((b ^ 2 - 1) * (n - 1) + b)
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have e1 : (c + 2) ^ 2 - 1 = (c + 1) * (c + 3) := by
    have : (c + 2) ^ 2 = (c + 1) * (c + 3) + 1 := by ring
    omega
  have e2 : c + 2 - 1 = c + 1 := by omega
  simp only [e1, e2, Nat.add_sub_cancel] at h ⊢
  have e3 : ((((c + 1) * (c + 3) * t + (c + 2) : ℕ) : ℤ) + 1) =
      ((c + 2 : ℕ) + 1 : ℤ) * (((c + 1) * t + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [e3] at h
  have hne : (((c + 2 : ℕ) : ℤ) + 1) ≠ 0 := by positivity
  exact (mul_dvd_mul_iff_left hne).mp h

/-- A212425 (b = 3, A(x) = sum a(n) x^(8n-5)): (2n-1) ∣ a(n). -/
theorem A212425_b3 (F : ℤ⟦X⟧) (h0 : constantCoeff F = 0) (hF : F = (X + F.subst F) ^ 3)
    (n : ℕ) (hn : 1 ≤ n) : ((2 * n - 1 : ℕ) : ℤ) ∣ coeff (8 * n - 5) F := by
  have h := A212425_main 3 (by norm_num) F h0 hF n hn
  have e1 : (3 - 1) * (n - 1) + 1 = 2 * n - 1 := by omega
  have e2 : (3 ^ 2 - 1) * (n - 1) + 3 = 8 * n - 5 := by omega
  rwa [e1, e2] at h

/-- A212392 (b = 2, A(x) = sum a(n) x^(3n-1)): n ∣ a(n). -/
theorem A212392_b2 (F : ℤ⟦X⟧) (h0 : constantCoeff F = 0) (hF : F = (X + F.subst F) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) : (n : ℤ) ∣ coeff (3 * n - 1) F := by
  have h := A212425_main 2 (by norm_num) F h0 hF n hn
  have e1 : (2 - 1) * (n - 1) + 1 = n := by omega
  have e2 : (2 ^ 2 - 1) * (n - 1) + 2 = 3 * n - 1 := by omega
  rwa [e1, e2] at h
