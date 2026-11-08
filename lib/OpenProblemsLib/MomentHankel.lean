import Mathlib

/-!
# Hankel matrices of constant terms of powers of a self-reciprocal Laurent polynomial

Laurent polynomials in several variables are `AddMonoidAlgebra ℝ G` for an additive commutative
group `G` of exponent vectors (`G = Fin m → ℤ` for `m` variables). `ct P` is the constant term
(coefficient of the exponent `0`) and `negRefl` is the ring map `x ↦ 1/x` (negate every exponent).

Main results.
* `ct_mul_self_of_refl` : if `negRefl Q = Q` then `ct (Q * Q)` is the sum of the squares of the
  coefficients of `Q` (since `ct (Q(x) Q(1/x))` pairs each coefficient with itself).
* `ct_mul_self_pos` : such a `Q ≠ 0` has `0 < ct (Q * Q)`.
* `hankel_posDef` : if `negRefl L = L` and `1, L, ..., L^(n-1)` are linearly independent over `ℝ`,
  the Hankel matrix `[ct (L^(i+j))]_{i,j<n}` is positive definite (`Matrix.PosDef`), so its
  determinant is positive (`Matrix.PosDef.det_pos`). Its quadratic form at `c` is
  `ct (Q * Q)` with `Q = Σ c_i L^i`.

Used by OEIS A225776 (Hankel determinants of `Σ_j C(k,j)^r`). Guide: `lib/docs/moment-hankel.md`.
-/

open Finset AddMonoidAlgebra

namespace OpenProblemsLib.MomentHankel


variable {G : Type*} [AddCommGroup G]

noncomputable def ct (P : AddMonoidAlgebra ℝ G) : ℝ := P.coeff 0

noncomputable def negRefl : AddMonoidAlgebra ℝ G →+* AddMonoidAlgebra ℝ G :=
  AddMonoidAlgebra.mapDomainRingHom ℝ (negAddMonoidHom : G →+ G)

theorem refl_single (g : G) (c : ℝ) : negRefl (single g c) = single (-g) c := by
  simp [negRefl, negAddMonoidHom]

theorem coeff_refl_neg (P : AddMonoidAlgebra ℝ G) (g : G) :
    (negRefl P).coeff (-g) = P.coeff g := by
  show (Finsupp.mapDomain (fun x : G => -x) P.coeff) (-g) = P.coeff g
  exact Finsupp.mapDomain_apply_of_injective neg_injective _ _

theorem refl_smul (a : ℝ) (P : AddMonoidAlgebra ℝ G) : negRefl (a • P) = a • negRefl P := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  simp [negRefl, AddMonoidAlgebra.coe_algebraMap]

theorem ct_sum {ι : Type*} (s : Finset ι) (f : ι → AddMonoidAlgebra ℝ G) :
    ct (∑ i ∈ s, f i) = ∑ i ∈ s, ct (f i) := by
  simp [ct, Finsupp.finsetSum_apply]

theorem ct_smul (a : ℝ) (P : AddMonoidAlgebra ℝ G) : ct (a • P) = a * ct P := by
  simp [ct]

theorem ct_mul (P R : AddMonoidAlgebra ℝ G) :
    ct (P * R) = ∑ a ∈ P.coeff.support, P.coeff a * R.coeff (-a) := by
  rw [ct, coeff_mul_apply_left, Finsupp.sum]
  simp

theorem ct_mul_self_of_refl (Q : AddMonoidAlgebra ℝ G) (hQ : negRefl Q = Q) :
    ct (Q * Q) = ∑ a ∈ Q.coeff.support, Q.coeff a ^ 2 := by
  rw [ct_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← coeff_refl_neg Q a, hQ, sq]

theorem ct_mul_self_pos (Q : AddMonoidAlgebra ℝ G) (hQ : negRefl Q = Q) (h0 : Q ≠ 0) :
    0 < ct (Q * Q) := by
  rw [ct_mul_self_of_refl Q hQ]
  have hne : Q.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa using h0
  obtain ⟨a, ha⟩ := hne
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨a, ha, by have := Finsupp.mem_support_iff.mp ha; positivity⟩

theorem form_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n →₀ ℝ) :
    (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) = ∑ i, ∑ j, x i * M i j * x j := by
  simp only [Finsupp.sum_fintype, star_trivial, zero_mul, mul_zero,
    Finset.sum_const_zero, implies_true]

theorem hankel_posDef (L : AddMonoidAlgebra ℝ G) (hL : negRefl L = L) (n : ℕ)
    (hind : ∀ c : Fin n → ℝ, ∑ i, c i • L ^ (i : ℕ) = 0 → c = 0) :
    (Matrix.of fun i j : Fin n => ct (L ^ ((i : ℕ) + j))).PosDef := by
  refine ⟨Matrix.IsHermitian.ext fun i j => by simp [add_comm], fun x hx => ?_⟩
  set Q : AddMonoidAlgebra ℝ G := ∑ i, x i • L ^ (i : ℕ) with hQdef
  have hform : (x.sum fun i xi => x.sum fun j xj =>
      star xi * (Matrix.of fun i j : Fin n => ct (L ^ ((i : ℕ) + j))) i j * xj) = ct (Q * Q) := by
    rw [form_eq, hQdef, Finset.sum_mul_sum, ct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, ← pow_add, ct_smul]
    simp [Matrix.of_apply]
    ring
  rw [hform]
  have hQ : negRefl Q = Q := by
    simp only [hQdef, map_sum, refl_smul, map_pow, hL]
  refine ct_mul_self_pos Q hQ ?_
  intro h0
  apply hx
  have := hind x (by rw [← hQdef]; exact h0)
  ext i
  simpa using congrFun this i

end OpenProblemsLib.MomentHankel
