/-
OEIS A225776, Mathlib proof: positivity of the Hankel determinants of
f(r, k) = Sum_{j=0..k} C(k, j)^r for every r >= 2.

Main theorem `A225776_pos`: for all r >= 2 and n >= 0,
  0 < det [f(r, i+j)]_{0 <= i, j <= n}   (determinant over ℤ).

Proof. Write r = m + 2 and work with Laurent polynomials in m+1 variables,
AddMonoidAlgebra ℝ (Fin (m+1) → ℤ). Let
  L = (1+x_0)...(1+x_m)(1 + 1/(x_0...x_m))   (`Lr m`).
* `ct_Lr_pow`: the constant term of L^k is Sum_b C(k,b)^(m+2) = f(r, k).
* `refl_Lr`: L(1/x) = L(x).
* `Lr_indep`: 1, L, ..., L^(n-1) are linearly independent: evaluating at
  x_0 = t, x_1 = ... = x_m = 1 gives 2^m (2 + t + 1/t) (`ev_Lr`), which is
  injective on t = 1, 2, 3, ... (`v_strictMono`), and a Vandermonde matrix with
  distinct nodes is invertible.
* `OpenProblemsLib.MomentHankel.hankel_posDef` (lib/OpenProblemsLib/MomentHankel.lean):
  for such L the quadratic form of [CT(L^(i+j))] at c is
  CT(Q(x) Q(1/x)) = (sum of squared coefficients of Q), Q = Sum c_i L^i, so the
  matrix is positive definite and its determinant is positive.

Checked here: the full statement for all r >= 2 and n >= 0.
Not checked here: the oddness of a(r, n)/2^n (Zhu-Sun, IJNT 14 (2018), Thm 1.1)
and the r = 3 statement a(n)/6^n odd.
-/
import Mathlib
import OpenProblemsLib.MomentHankel

open Finset AddMonoidAlgebra

open OpenProblemsLib.MomentHankel

/-- `f(r, k) = ∑_{j=0}^{k} C(k, j)^r`. -/
def f (r k : ℕ) : ℕ := ∑ j ∈ range (k + 1), (k.choose j) ^ r

theorem pow_one_add_single {G : Type*} [AddCommGroup G] (g : G) (k : ℕ) :
    (1 + single g (1 : ℝ)) ^ k = ∑ a ∈ range (k + 1), single (a • g) ((k.choose a : ℕ) : ℝ) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [single_pow, AddMonoidAlgebra.natCast_def, single_mul_single]

/-- The Laurent polynomial `(1+x_0)...(1+x_m)(1 + 1/(x_0...x_m))` in `m+1` variables. -/
noncomputable def Lr (m : ℕ) : AddMonoidAlgebra ℝ (Fin (m + 1) → ℤ) :=
  (∏ i, (1 + single (Pi.single i 1) 1)) * (1 + single (fun _ => -1) 1)

theorem exps_eq_zero_iff (m : ℕ) (p : Fin (m + 1) → ℕ) (b : ℕ) :
    ((∑ i, p i • (Pi.single i (1 : ℤ) : Fin (m + 1) → ℤ)) + b • (fun _ => (-1 : ℤ))) = 0 ↔
      p = fun _ => b := by
  have hs : (∑ i, p i • (Pi.single i (1 : ℤ) : Fin (m + 1) → ℤ)) = fun j => (p j : ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs, funext_iff, funext_iff]
  refine forall_congr' fun j => ?_
  simp
  omega

theorem ct_Lr_pow (m k : ℕ) :
    ct ((Lr m) ^ k) = ∑ b ∈ range (k + 1), ((k.choose b : ℕ) : ℝ) ^ (m + 2) := by
  classical
  rw [Lr, mul_pow, ← Finset.prod_pow]
  simp_rw [pow_one_add_single]
  rw [Finset.prod_univ_sum, Finset.sum_mul_sum]
  simp only [prod_single, single_mul_single]
  rw [ct]
  simp only [coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [coeff_single, Finsupp.single_apply,
    exps_eq_zero_iff, Finset.sum_ite_eq']
  have hm : (fun _ => b) ∈ Fintype.piFinset fun _ : Fin (m + 1) => range (k + 1) :=
    Fintype.mem_piFinset.mpr fun _ => hb
  simp [hm, Finset.prod_const, pow_succ]

theorem refl_Lr (m : ℕ) : negRefl (Lr m) = Lr m := by
  let Y : Fin (m + 1) → AddMonoidAlgebra ℝ (Fin (m + 1) → ℤ) := fun i => single (Pi.single i 1) 1
  let Yi : Fin (m + 1) → AddMonoidAlgebra ℝ (Fin (m + 1) → ℤ) :=
    fun i => single (-Pi.single i 1) 1
  let W : AddMonoidAlgebra ℝ (Fin (m + 1) → ℤ) := single (fun _ => 1) 1
  let Wi : AddMonoidAlgebra ℝ (Fin (m + 1) → ℤ) := single (fun _ => -1) 1
  have hL : Lr m = (∏ i, (1 + Y i)) * (1 + Wi) := rfl
  have h1 : ∀ i, 1 + Y i = Y i * (1 + Yi i) := by
    intro i
    simp only [Y, Yi, mul_add, mul_one, single_mul_single, add_neg_cancel]
    rw [← AddMonoidAlgebra.one_def]
    exact add_comm _ _
  have h2 : ∏ i, Y i = W := by
    simp only [Y, W, prod_single, Finset.univ_sum_single, Finset.prod_const_one]
  have h3 : W * (1 + Wi) = 1 + W := by
    simp only [W, Wi, mul_add, mul_one, single_mul_single]
    have : ((fun _ => (1 : ℤ)) + fun _ => -1 : Fin (m + 1) → ℤ) = 0 := by
      funext; simp
    rw [this, ← AddMonoidAlgebra.one_def]
    exact add_comm _ _
  have hneg : (-(fun _ => (-1 : ℤ)) : Fin (m + 1) → ℤ) = fun _ => 1 := by
    funext; simp
  have hr : negRefl (Lr m) = (∏ i, (1 + Yi i)) * (1 + W) := by
    simp only [Lr, map_mul, map_prod, map_add, map_one, refl_single, hneg, Yi, W]
  rw [hr, hL, Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib, h2, ← h3]
  ring

noncomputable def phi (m : ℕ) (t : ℝ) (ht : t ≠ 0) : Multiplicative (Fin (m + 1) → ℤ) →* ℝ where
  toFun e := t ^ (e.toAdd 0)
  map_one' := by simp
  map_mul' a b := by simp [zpow_add₀ ht]

noncomputable def ev (m : ℕ) (t : ℝ) (ht : t ≠ 0) : AddMonoidAlgebra ℝ (Fin (m + 1) → ℤ) →ₐ[ℝ] ℝ :=
  AddMonoidAlgebra.lift ℝ ℝ (Fin (m + 1) → ℤ) (phi m t ht)

theorem ev_Lr (m : ℕ) (t : ℝ) (ht : t ≠ 0) : ev m t ht (Lr m) = 2 ^ m * (2 + t + t⁻¹) := by
  simp [ev, Lr, phi, Fin.prod_univ_succ, Fin.succ_ne_zero]
  field_simp
  ring

theorem v_strictMono : StrictMono fun s : ℕ => ((s : ℝ) + 1) + ((s : ℝ) + 1)⁻¹ := by
  refine strictMono_nat_of_lt_succ fun s => ?_
  have h1 : ((s : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [s.cast_nonneg (α := ℝ)])
  have h2 : 0 < (((s + 1 : ℕ) : ℝ) + 1)⁻¹ := by positivity
  push_cast at *
  linarith

theorem Lr_indep (m n : ℕ) (c : Fin n → ℝ) (h : ∑ i, c i • (Lr m) ^ (i : ℕ) = 0) : c = 0 := by
  have ht : ∀ j : Fin n, ((j : ℕ) : ℝ) + 1 ≠ 0 := fun j => by positivity
  refine Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    (f := fun j => 2 ^ m * (2 + (((j : ℕ) : ℝ) + 1) + (((j : ℕ) : ℝ) + 1)⁻¹)) ?_ ?_
  · intro a b hab
    have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
    have := mul_left_cancel₀ h2 hab
    have hv : ((a : ℕ) : ℝ) + 1 + (((a : ℕ) : ℝ) + 1)⁻¹ = ((b : ℕ) : ℝ) + 1 + (((b : ℕ) : ℝ) + 1)⁻¹ := by
      linarith
    exact Fin.ext (v_strictMono.injective hv)
  · intro j
    have := congrArg (ev m _ (ht j)) h
    simpa [map_sum, map_pow, ev_Lr] using this

/-- **A225776, positivity.** For every `r ≥ 2` and `n ≥ 0` the Hankel determinant
`det [f(r, i+j)]_{0 ≤ i, j ≤ n}` is positive. -/
theorem A225776_pos (r n : ℕ) (hr : 2 ≤ r) :
    0 < (Matrix.of fun i j : Fin (n + 1) => ((f r ((i : ℕ) + j) : ℕ) : ℤ)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hdet := (hankel_posDef (Lr m) (refl_Lr m) (n + 1) (Lr_indep m (n + 1))).det_pos
  have hmat : (Matrix.of fun i j : Fin (n + 1) => ct ((Lr m) ^ ((i : ℕ) + j))) =
      (Matrix.of fun i j : Fin (n + 1) => ((f (m + 2) ((i : ℕ) + j) : ℕ) : ℤ)).map
        (Int.castRingHom ℝ) := by
    ext i j
    simp [ct_Lr_pow, f]
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
  exact Int.cast_pos.mp hdet
