import Mathlib

/-
AIM workshop "Spectra of families of matrices described by graphs, digraphs and sign
patterns" (2006), open questions by I.-J. Kim and A. W. Wehe, section 3, energy Q2:
is there a graph G with E(G - e) = E(G) + 2 for some edge e?  Answer: no.

Definitions.
* `energy X hX`: sum of |eigenvalues| of a real symmetric matrix (Mathlib's
  `Matrix.IsHermitian.eigenvalues`).
* `energyG G`: energy of the adjacency matrix `G.adjMatrix ℝ` of a simple graph on a
  finite vertex type; `G.deleteEdges {s(u, v)}` is G - e.
* `IsContr W`: ‖W x‖² ≤ ‖x‖² for all x; `sgn hX = U diag(±1) Uᵀ` (eigenvector matrix U).

Main theorems.
* `aim_energy_Q2 : G.Adj u v → energyG (G.deleteEdges {s(u, v)}) < energyG G + 2`,
  and `aim_energy_Q2_ne` (≠).
* `energy_delete_lt`: the matrix form (A symmetric, A u v = A v u = 1, A' = A - (E_uv + E_vu)).
Route: `trace_le` (tr(W X) ≤ E(X) for a contraction W, via the spectral theorem and
2 a·b ≤ a·a + b·b); `sgn_contr`, `trace_sgn` (tr(sgn(X) X) = E(X)); with W = sgn(A'),
E(A') = tr(W A) - 2 W_uv; if W_uv = -1 then `col_sq_le` forces columns u, v of W to be
-e_v, -e_u, and W + (E_uv + E_vu) is a contraction with trace against A equal to E(A'),
so E(A') ≤ E(A).

Not checked here: Q1 (the known theorem of Day and So, cited in the README).
-/

namespace AimEnergy

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Energy of a real symmetric matrix: the sum of |eigenvalues|. -/
noncomputable def energy (X : Matrix n n ℝ) (hX : X.IsHermitian) : ℝ := ∑ i, |hX.eigenvalues i|

/-- Contraction: ‖W x‖² ≤ ‖x‖² for all x. -/
def IsContr (W : Matrix n n ℝ) : Prop := ∀ x : n → ℝ, (W *ᵥ x) ⬝ᵥ (W *ᵥ x) ≤ x ⬝ᵥ x

omit [DecidableEq n] in
lemma two_mul_dot_le (a b : n → ℝ) : 2 * (a ⬝ᵥ b) ≤ a ⬝ᵥ a + b ⬝ᵥ b := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (a i - b i)])

omit [DecidableEq n] in
lemma neg_two_mul_dot_le (a b : n → ℝ) : -(2 * (a ⬝ᵥ b)) ≤ a ⬝ᵥ a + b ⬝ᵥ b := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (a i + b i)])

/-- The eigenvector matrix U, with A = U D Uᵀ. -/
noncomputable abbrev U {X : Matrix n n ℝ} (hX : X.IsHermitian) : Matrix n n ℝ :=
  (hX.eigenvectorUnitary : Matrix n n ℝ)

lemma spec {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    X = U hX * diagonal hX.eigenvalues * (U hX)ᵀ := by
  have h := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  conv_lhs => rw [h]
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

lemma UtU {X : Matrix n n ℝ} (hX : X.IsHermitian) : (U hX)ᵀ * U hX = 1 := by
  have := Matrix.UnitaryGroup.star_mul_self hX.eigenvectorUnitary
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma UUt {X : Matrix n n ℝ} (hX : X.IsHermitian) : U hX * (U hX)ᵀ = 1 := by
  have := (Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2)
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- Key inequality: tr(W X) ≤ E(X) for a contraction W. -/
lemma trace_le (X W : Matrix n n ℝ) (hX : X.IsHermitian) (hW : IsContr W) :
    (W * X).trace ≤ energy X hX := by
  set V := U hX
  have h1 : (W * X).trace = (Vᵀ * W * V * diagonal hX.eigenvalues).trace := by
    conv_lhs => rw [spec hX]
    rw [show W * (V * diagonal hX.eigenvalues * Vᵀ) = (W * V * diagonal hX.eigenvalues) * Vᵀ by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h1]
  unfold energy
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  refine Finset.sum_le_sum (fun i _ => ?_)
  set c : n → ℝ := fun j => V j i
  have hm : (Vᵀ * W * V) i i = c ⬝ᵥ (W *ᵥ c) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mulVec, c, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
  have hc : c ⬝ᵥ c = 1 := by
    have := congrFun (congrFun (UtU hX) i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
    simpa only [dotProduct, c] using this
  have hb : |c ⬝ᵥ (W *ᵥ c)| ≤ 1 := by
    have h2 := hW c
    rw [abs_le]
    constructor <;> nlinarith [two_mul_dot_le c (W *ᵥ c), neg_two_mul_dot_le c (W *ᵥ c)]
  rw [hm]
  calc c ⬝ᵥ (W *ᵥ c) * hX.eigenvalues i ≤ |c ⬝ᵥ (W *ᵥ c) * hX.eigenvalues i| := le_abs_self _
    _ = |c ⬝ᵥ (W *ᵥ c)| * |hX.eigenvalues i| := abs_mul _ _
    _ ≤ 1 * |hX.eigenvalues i| := by gcongr
    _ = |hX.eigenvalues i| := one_mul _


/-- Sign matrix of X: U diag(±1) Uᵀ with s_i λ_i = |λ_i|. -/
noncomputable def sgn {X : Matrix n n ℝ} (hX : X.IsHermitian) : Matrix n n ℝ :=
  U hX * diagonal (fun i => if hX.eigenvalues i < 0 then -1 else 1) * (U hX)ᵀ

lemma sgn_symm {X : Matrix n n ℝ} (hX : X.IsHermitian) : (sgn hX)ᵀ = sgn hX := by
  simp [sgn, Matrix.transpose_mul, Matrix.mul_assoc]

lemma sgn_mul_self {X : Matrix n n ℝ} (hX : X.IsHermitian) : sgn hX * sgn hX = 1 := by
  set D := diagonal (fun i => if hX.eigenvalues i < 0 then (-1 : ℝ) else 1)
  have hD : D * D = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; split_ifs <;> norm_num
  calc sgn hX * sgn hX = U hX * D * ((U hX)ᵀ * U hX) * D * (U hX)ᵀ := by
        simp only [sgn, D, Matrix.mul_assoc]
    _ = U hX * (D * D) * (U hX)ᵀ := by rw [UtU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hD, Matrix.mul_one, UUt]

lemma sgn_contr {X : Matrix n n ℝ} (hX : X.IsHermitian) : IsContr (sgn hX) := by
  intro x
  have h : sgn hX *ᵥ (sgn hX *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, sgn_mul_self, Matrix.one_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, sgn_symm, h]

lemma trace_sgn {X : Matrix n n ℝ} (hX : X.IsHermitian) : (sgn hX * X).trace = energy X hX := by
  have h0 : (sgn hX * X).trace = (sgn hX * (U hX * diagonal hX.eigenvalues * (U hX)ᵀ)).trace := by
    rw [← spec hX]
  rw [h0, show sgn hX * (U hX * diagonal hX.eigenvalues * (U hX)ᵀ) =
      U hX * (diagonal (fun i => if hX.eigenvalues i < 0 then (-1 : ℝ) else 1) * ((U hX)ᵀ * U hX) *
        diagonal hX.eigenvalues) * (U hX)ᵀ by simp only [sgn, Matrix.mul_assoc]]
  rw [UtU, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, UtU, Matrix.one_mul,
    diagonal_mul_diagonal, Matrix.trace_diagonal]
  unfold energy
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

lemma col_sq_le (W : Matrix n n ℝ) (hW : IsContr W) (u : n) : ∑ j, W j u ^ 2 ≤ 1 := by
  have := hW (Pi.single u 1)
  have h1 : (Pi.single u (1 : ℝ)) ⬝ᵥ (Pi.single u 1) = 1 := by simp [dotProduct, Pi.single_apply]
  rw [h1] at this
  simpa [Matrix.mulVec_single_one, dotProduct, sq] using this

/-- The matrix of the single edge uv. -/
def Bm (u v : n) : Matrix n n ℝ := fun i j => if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then 1 else 0

lemma trace_mul_Bm (M : Matrix n n ℝ) (u v : n) (huv : u ≠ v) :
    (M * Bm u v).trace = M v u + M u v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_eq_add v u (Ne.symm huv)]
  · congr 1
    · rw [Fintype.sum_eq_single u]
      · simp [Bm]
      · intro j hj; simp [Bm, hj, huv.symm]
    · rw [Fintype.sum_eq_single v]
      · simp [Bm]
      · intro j hj; simp [Bm, hj, huv]
  · intro i ⟨hiv, hiu⟩
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [Bm, hiv, hiu]

lemma trace_Bm_mul (M : Matrix n n ℝ) (u v : n) (huv : u ≠ v) :
    (Bm u v * M).trace = M v u + M u v := by
  rw [Matrix.trace_mul_comm, trace_mul_Bm M u v huv]

/-- Deleting a +1 entry pair uv from a real symmetric matrix raises the energy by less than 2. -/
theorem energy_delete_lt (A A' : Matrix n n ℝ) (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    (u v : n) (huv : u ≠ v) (hAuv : A u v = 1) (hAvu : A v u = 1) (hdef : A' = A - Bm u v) :
    energy A' hA' < energy A hA + 2 := by
  set W := sgn hA' with hWdef
  have hWc : IsContr W := sgn_contr hA'
  have hWs : ∀ i j, W j i = W i j := fun i j => by
    have := congrFun (congrFun (sgn_symm hA') i) j
    simpa [Matrix.transpose_apply] using this
  have hE : energy A' hA' = (W * A).trace - 2 * W u v := by
    rw [← trace_sgn hA', ← hWdef]
    have h1 : W * A' = W * (A - Bm u v) := congrArg (W * ·) hdef
    rw [h1, Matrix.mul_sub, Matrix.trace_sub, trace_mul_Bm W u v huv, hWs u v]
    ring
  have hle : (W * A).trace ≤ energy A hA := trace_le A W hA hWc
  by_cases hw : -1 < W u v
  · rw [hE]; linarith
  · push Not at hw
    have cv := col_sq_le W hWc v
    have cu := col_sq_le W hWc u
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)] at cv
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at cu
    have hnn1 : 0 ≤ ∑ j ∈ univ.erase u, W j v ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hnn2 : 0 ≤ ∑ j ∈ univ.erase v, W j u ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hvu : W v u = W u v := hWs u v
    have hm1 : W u v = -1 := by nlinarith
    have z1 : ∑ j ∈ univ.erase u, W j v ^ 2 = 0 := by rw [hm1] at cv; nlinarith
    have z2 : ∑ j ∈ univ.erase v, W j u ^ 2 = 0 := by rw [hvu, hm1] at cu; nlinarith
    have colv : ∀ j, j ≠ u → W j v = 0 := by
      intro j hj
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (W j v))).mp z1 j
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have colu : ∀ j, j ≠ v → W j u = 0 := by
      intro j hj
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (W j u))).mp z2 j
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    set W' := W + Bm u v
    have hW'u : ∀ i, W' i u = 0 := by
      intro i
      simp only [W', Matrix.add_apply, Bm]
      by_cases hi : i = v
      · rw [hi, hvu, hm1]; simp
      · rw [colu i hi]; simp [hi, huv]
    have hW'v : ∀ i, W' i v = 0 := by
      intro i
      simp only [W', Matrix.add_apply, Bm]
      by_cases hi : i = u
      · rw [hi, hm1]; simp
      · rw [colv i hi]; simp [hi, Ne.symm huv]
    have hc' : IsContr W' := by
      intro x
      set x' : n → ℝ := fun j => if j = u ∨ j = v then 0 else x j
      have hx : W' *ᵥ x = W *ᵥ x' := by
        funext i
        simp only [mulVec, dotProduct]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j = u ∨ j = v
        · rcases hj with hj | hj
          · rw [hj, hW'u]; simp [x']
          · rw [hj, hW'v]; simp [x']
        · push Not at hj
          simp only [W', Matrix.add_apply, Bm, x', hj.1, hj.2, and_false, or_false, ite_false,
            add_zero]
      rw [hx]
      refine (hWc x').trans ?_
      simp only [dotProduct, x']
      refine Finset.sum_le_sum (fun j _ => ?_)
      split_ifs <;> nlinarith [mul_self_nonneg (x j)]
    have htr : (W' * A).trace = (W * A).trace + 2 := by
      simp only [W', Matrix.add_mul, Matrix.trace_add, trace_Bm_mul A u v huv, hAuv, hAvu]
      ring
    have := trace_le A W' hA hc'
    rw [hE]
    linarith


/-- Energy of a simple graph on a finite vertex type: sum of |adjacency eigenvalues|. -/
noncomputable def energyG {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  energy (G.adjMatrix ℝ) (G.isHermitian_adjMatrix ℝ)

/-- AIM energy Q2: no graph G and edge e = uv have E(G - e) = E(G) + 2; indeed E(G - e) < E(G) + 2. -/
theorem aim_energy_Q2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) [DecidableRel (G.deleteEdges {s(u, v)}).Adj]
    (h : G.Adj u v) : energyG (G.deleteEdges {s(u, v)}) < energyG G + 2 := by
  unfold energyG
  have huv : u ≠ v := G.ne_of_adj h
  refine energy_delete_lt (G.adjMatrix ℝ) ((G.deleteEdges {s(u, v)}).adjMatrix ℝ) _ _ u v huv
    (by simp [h]) (by simp [h.symm]) ?_
  ext i j
  simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    Sym2.eq_iff, Matrix.sub_apply, Bm]
  by_cases hij : G.Adj i j
  · by_cases he : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
    · simp [hij, he]
    · simp [hij, he]
  · have he : ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hij h
      · exact hij h.symm
    simp [hij, he]

theorem aim_energy_Q2_ne {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) [DecidableRel (G.deleteEdges {s(u, v)}).Adj] (h : G.Adj u v) : energyG (G.deleteEdges {s(u, v)}) ≠ energyG G + 2 :=
  ne_of_lt (aim_energy_Q2 G u v h)
