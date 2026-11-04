import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Discriminant of the quadratic number field Q(√d)

`QuadraticAlgebra ℚ a b` is `ℚ[ω]` with `ω² = a + b·ω`; it is a field when `X² - bX - a` has no
rational root (Mathlib), and `QuadraticAlgebra ℚ d 0` is Q(√d).

* `numberField`: these fields are number fields (instance);
* `trace_norm_int`: an element integral over ℤ has integer trace and norm;
* `closure_zero`, `closure_one`: for squarefree d, every integral element of
  `QuadraticAlgebra ℚ d 0` (d ≡ 2, 3 mod 4), resp. `QuadraticAlgebra ℚ a 1` (d = 1 + 4a),
  comes from the order `QuadraticAlgebra ℤ d 0` = Z[√d], resp. `QuadraticAlgebra ℤ a 1` =
  Z[(1+√d)/2];
* `numberField_discr_of`: if the order `QuadraticAlgebra ℤ a b` is the full ring of integers,
  `NumberField.discr` of `QuadraticAlgebra ℚ a b` is `b² + 4a` (trace form on the basis 1, ω);
* `discr_sqrt`: for squarefree d not a square in ℚ, `NumberField.discr (QuadraticAlgebra ℚ d 0)`
  is d if d ≡ 1 (mod 4) and 4d otherwise.

Integrality: x integral ⇒ its conjugate integral ⇒ trace t and norm m integral rationals,
hence integers; then disc·(im x)² = t² - 4m and squarefreeness give im x (or 2·im x) ∈ ℤ, and a
parity check mod 4 gives the rest.
-/

namespace OpenProblemsLib.R5Quadratic

open QuadraticAlgebra NumberField

theorem int_of_squarefree_mul_sq {d : ℤ} (hd : Squarefree d) {u : ℚ} {k : ℤ}
    (h : (d : ℚ) * u ^ 2 = k) : ∃ m : ℤ, u = m := by
  have hden : (u.den : ℚ) ≠ 0 := by positivity
  have key : d * u.num ^ 2 = k * (u.den : ℤ) ^ 2 := by
    have hu : u = u.num / u.den := (Rat.num_div_den u).symm
    have : (d : ℚ) * (u.num : ℚ) ^ 2 = k * (u.den : ℚ) ^ 2 := by
      rw [hu] at h
      field_simp at h
      linarith
    exact_mod_cast this
  have hc : IsCoprime ((u.den : ℤ) ^ 2) (u.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.coprime_comm] using u.reduced
  have hdvd : (u.den : ℤ) ^ 2 ∣ d := hc.dvd_of_dvd_mul_right ⟨k, by rw [key]; ring⟩
  have hunit : IsUnit (u.den : ℤ) := hd _ (by rw [← sq]; exact hdvd)
  have h1 : u.den = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> omega
  exact ⟨u.num, (Rat.coe_int_num_of_den_eq_one h1).symm⟩

variable {R : Type*} [CommRing R] {a b : R}

theorem algebra_trace_eq (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = trace z := by
  rw [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, basis_repr_apply, trace_def]
  ring


instance numberField {a b : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    NumberField (QuadraticAlgebra ℚ a b) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := inferInstance

theorem algebraMap_trace {K : Type*} [Field K] {a b : K} (z : QuadraticAlgebra K a b) :
    z + star z = algebraMap K _ (trace z) := by
  ext <;> simp [trace_def]
  ring

theorem trace_norm_int {a b : ℤ} [Fact (∀ r : ℚ, r ^ 2 ≠ (a : ℚ) + b * r)]
    {x : QuadraticAlgebra ℚ a b} (hx : IsIntegral ℤ x) :
    (∃ t : ℤ, trace x = t) ∧ ∃ m : ℤ, norm x = m := by
  have hs : IsIntegral ℤ (star x) := by
    simpa [starRingEnd_apply] using hx.map (starRingEnd (QuadraticAlgebra ℚ a b)).toIntAlgHom
  have ht : IsIntegral ℤ (trace x) := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := QuadraticAlgebra ℚ a b), ← algebraMap_trace]
    exact hx.add hs
  have hn : IsIntegral ℤ (norm x) := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := QuadraticAlgebra ℚ a b),
      algebraMap_norm_eq_mul_star]
    exact hx.mul hs
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  exact ⟨⟨t, by simp [← ht]⟩, ⟨m, by simp [← hm]⟩⟩

theorem algebra_discr_basis {a b : ℤ} :
    Algebra.discr ℤ (basis a b) = QuadraticAlgebra.discr a b := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, algebra_trace_eq, trace_def,
    basis_apply_zero, basis_apply_one, QuadraticAlgebra.discr_def]
  ring


theorem closure_zero {d : ℤ} (hd : Squarefree d) (h4 : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + ((0 : ℤ) : ℚ) * r)]
    (x : QuadraticAlgebra ℚ d (0 : ℤ)) (hx : IsIntegral ℤ x) :
    ∃ y : QuadraticAlgebra ℤ d 0, algebraMap _ (QuadraticAlgebra ℚ d (0 : ℤ)) y = x := by
  obtain ⟨⟨t, ht⟩, ⟨m, hm⟩⟩ := trace_norm_int hx
  rw [trace_def] at ht
  rw [norm_def] at hm
  simp only [Int.cast_zero, zero_mul, add_zero] at ht hm
  have h2 : (d : ℚ) * (2 * x.im) ^ 2 = ((t ^ 2 - 4 * m : ℤ) : ℚ) := by
    push_cast
    rw [← ht, ← hm]
    ring
  obtain ⟨v, hv⟩ := int_of_squarefree_mul_sq hd h2
  have key : t ^ 2 - d * v ^ 2 = 4 * m := by
    have : (t : ℚ) ^ 2 - d * (v : ℚ) ^ 2 = 4 * m := by
      rw [← hv, ← ht, ← hm]
      ring
    exact_mod_cast this
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' t <;> obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' v
  · refine ⟨⟨k, l⟩, ?_⟩
    push_cast at ht hv
    refine QuadraticAlgebra.ext ?_ ?_ <;>
      simp only [QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap] <;>
      push_cast <;> linarith
  all_goals ring_nf at key; omega

theorem closure_one {a : ℤ} (hd : Squarefree (1 + 4 * a))
    [Fact (∀ r : ℚ, r ^ 2 ≠ (a : ℚ) + ((1 : ℤ) : ℚ) * r)]
    (x : QuadraticAlgebra ℚ a (1 : ℤ)) (hx : IsIntegral ℤ x) :
    ∃ y : QuadraticAlgebra ℤ a 1, algebraMap _ (QuadraticAlgebra ℚ a (1 : ℤ)) y = x := by
  obtain ⟨⟨t, ht⟩, ⟨m, hm⟩⟩ := trace_norm_int hx
  rw [trace_def] at ht
  rw [norm_def] at hm
  simp only [Int.cast_one, one_mul] at ht hm
  have h2 : ((1 + 4 * a : ℤ) : ℚ) * x.im ^ 2 = ((t ^ 2 - 4 * m : ℤ) : ℚ) := by
    push_cast
    rw [← ht, ← hm]
    ring
  obtain ⟨v, hv⟩ := int_of_squarefree_mul_sq hd h2
  have key : t ^ 2 - (1 + 4 * a) * v ^ 2 = 4 * m := by
    have : (t : ℚ) ^ 2 - (1 + 4 * a) * (v : ℚ) ^ 2 = 4 * m := by
      rw [← hv, ← ht, ← hm]
      ring
    exact_mod_cast this
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' t <;> obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' v
  · refine ⟨⟨k - l, 2 * l⟩, ?_⟩
    push_cast at ht hv
    refine QuadraticAlgebra.ext ?_ ?_ <;>
      simp only [QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap] <;>
      push_cast <;> linarith
  rotate_left 2
  · refine ⟨⟨k - l, 2 * l + 1⟩, ?_⟩
    push_cast at ht hv
    refine QuadraticAlgebra.ext ?_ ?_ <;>
      simp only [QuadraticAlgebra.Int.re_algebraMap, QuadraticAlgebra.Int.im_algebraMap] <;>
      push_cast <;> linarith
  all_goals ring_nf at key; omega

theorem isIntegralClosure_of {a b : ℤ} [Fact (∀ r : ℚ, r ^ 2 ≠ (a : ℚ) + b * r)]
    (hcl : ∀ x : QuadraticAlgebra ℚ a b, IsIntegral ℤ x →
      ∃ y : QuadraticAlgebra ℤ a b, algebraMap _ _ y = x) :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) where
  algebraMap_injective := FaithfulSMul.algebraMap_injective _ _
  isIntegral_iff := fun {x} =>
    ⟨hcl x, by rintro ⟨y, rfl⟩; exact (Algebra.IsIntegral.isIntegral y).algebraMap⟩

theorem numberField_discr_of {a b : ℤ} [Fact (∀ r : ℚ, r ^ 2 ≠ (a : ℚ) + b * r)]
    (hcl : ∀ x : QuadraticAlgebra ℚ a b, IsIntegral ℤ x →
      ∃ y : QuadraticAlgebra ℤ a b, algebraMap _ _ y = x) :
    NumberField.discr (QuadraticAlgebra ℚ a b) = QuadraticAlgebra.discr a b := by
  have := isIntegralClosure_of hcl
  let e := IsIntegralClosure.equiv ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)
    (𝓞 (QuadraticAlgebra ℚ a b))
  rw [← NumberField.discr_eq_discr _ ((basis a b).map e.toLinearEquiv), Module.Basis.coe_map]
  rw [← algebra_discr_basis]
  exact (Algebra.discr_eq_discr_of_algEquiv _ e).symm

theorem not_isSquare_of_squarefree {d : ℤ} (hd : Squarefree d) (h1 : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  rintro ⟨r, hr⟩
  obtain ⟨m, rfl⟩ := int_of_squarefree_mul_sq hd (u := r) (k := d ^ 2) 
    (by push_cast; rw [hr]; ring)
  have hdm : d = m * m := by exact_mod_cast hr
  have hu : IsUnit m := hd m ⟨1, by rw [hdm, mul_one]⟩
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp_all

theorem emod_four_ne_zero {d : ℤ} (hd : Squarefree d) : d % 4 ≠ 0 := by
  intro h
  have := hd 2 ⟨d / 4, by omega⟩
  simp [Int.isUnit_iff] at this

theorem discr_sqrt {d : ℤ} (hd : Squarefree d) [Fact (¬ IsSquare (d : ℚ))] :
    NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = if d % 4 = 1 then d else 4 * d := by
  split_ifs with h
  · obtain ⟨a, rfl⟩ : ∃ a, d = 1 + 4 * a := ⟨(d - 1) / 4, by omega⟩
    have hD : QuadraticAlgebra.discr ((a : ℤ) : ℚ) ((1 : ℤ) : ℚ) = (((1 + 4 * a : ℤ)) : ℚ) := by
      rw [QuadraticAlgebra.discr_def]
      push_cast
      ring
    have : Fact (¬ IsSquare (QuadraticAlgebra.discr ((a : ℤ) : ℚ) ((1 : ℤ) : ℚ))) :=
      ⟨hD ▸ Fact.out⟩
    have : Fact (∀ r : ℚ, r ^ 2 ≠ (a : ℚ) + ((1 : ℤ) : ℚ) * r) := inferInstance
    obtain ⟨e⟩ : Nonempty (QuadraticAlgebra ℚ (((1 + 4 * a : ℤ)) : ℚ) 0 ≃ₐ[ℚ]
        QuadraticAlgebra ℚ ((a : ℤ) : ℚ) ((1 : ℤ) : ℚ)) := by
      let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
      rw [nonempty_algEquiv_iff_of_invertible_two]
      refine ⟨Units.mk0 2 two_ne_zero, ?_⟩
      rw [hD, QuadraticAlgebra.discr_def, Units.val_mk0]
      push_cast
      ring
    rw [NumberField.discr_eq_discr_of_algEquiv _ e, numberField_discr_of (closure_one hd),
      QuadraticAlgebra.discr_def]
    ring
  · have h4 : d % 4 = 2 ∨ d % 4 = 3 := by have := emod_four_ne_zero hd; omega
    have : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + ((0 : ℤ) : ℚ) * r) :=
      ⟨by simpa using (Fact.out : ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)⟩
    obtain ⟨e⟩ : Nonempty (QuadraticAlgebra ℚ (d : ℚ) 0 ≃ₐ[ℚ]
        QuadraticAlgebra ℚ ((d : ℤ) : ℚ) ((0 : ℤ) : ℚ)) := by
      let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
      rw [nonempty_algEquiv_iff_of_invertible_two]
      exact ⟨1, by simp⟩
    rw [NumberField.discr_eq_discr_of_algEquiv _ e, numberField_discr_of (closure_zero hd h4),
      QuadraticAlgebra.discr_def]
    ring

end OpenProblemsLib.R5Quadratic
