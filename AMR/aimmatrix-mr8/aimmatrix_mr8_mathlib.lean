import Mathlib

/-
AIM workshop 2006, open question Q8 (I.-J. Kim, A. W. Wehe, "Open Questions",
2007): for each tree T other than the star K_{1,n-1}, does the sequence
mr(T), mr(T^2), mr(T^3), ... decrease strictly until it hits 2?
Here T^j has an edge uv (u ≠ v) iff T has a walk of length exactly j from u
to v (the "strict power" of DeAlba et al., ELA 23 (2012)), and mr(G) is the
least rank of a real symmetric matrix whose off-diagonal entry (u,v) is
nonzero exactly when uv is an edge (diagonal free).

Answer: no.  T = the path 0-1-2-3-4 with two leaves 5, 6 attached at 4
(7 vertices, not a star).  Then mr(T) = 5, mr(T^2) = 4, mr(T^3) = 4.

Definitions.
* `adjT`: the tree, `walk r i j`: a walk of length exactly r from i to j,
  `spow r i j`: i ≠ j and `walk r i j` (the strict power).
* `IsPat G A`: A symmetric and, off the diagonal, `A i j ≠ 0 ↔ G i j`.
* `mr G`: `sInf` of the ranks of real matrices with `IsPat G`.

Main theorem.
* `aimmatrix_mr8`: T is not a star, mr(T) = 5, mr(T^2) = 4, mr(T^3) = 4, so
  the sequence is not strictly decreasing before reaching 2.

Route.  Upper bounds: explicit integer matrices written as U * W with U of
width 5 (T) or 4 (T^2, T^3).  Lower bounds: a 5x5 (T) or 4x4 (T^2, T^3)
submatrix that, for every matrix with the pattern, is upper triangular with
nonzero diagonal (its entries below the diagonal are non-edges, its diagonal
entries are edges), so it has full rank, and `Matrix.rank_submatrix_le`.

Not checked in this file: that this reading of "power" and "mr" is the one
of the source (it is the definition printed in the source, Q6-Q8).
-/

namespace AimMr8

/-- The tree: path 0-1-2-3-4, leaves 5 and 6 at vertex 4. -/
def adjT (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈
    [(0,1),(1,0),(1,2),(2,1),(2,3),(3,2),(3,4),(4,3),(4,5),(5,4),(4,6),(6,4)])

/-- A walk of length exactly `r` from `i` to `j` in the tree. -/
def walk : ℕ → Fin 7 → Fin 7 → Bool
  | 0, i, j => decide (i = j)
  | r + 1, i, j => (List.finRange 7).any (fun k => adjT i k && walk r k j)

/-- Strict power `T^r`. -/
def spow (r : ℕ) (i j : Fin 7) : Bool := decide (i ≠ j) && walk r i j

/-- Real symmetric matrices with off-diagonal zero pattern `G`. -/
def IsPat (G : Fin 7 → Fin 7 → Bool) (A : Matrix (Fin 7) (Fin 7) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧ ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G i j = true)

/-- Minimum rank. -/
noncomputable def mr (G : Fin 7 → Fin 7 → Bool) : ℕ :=
  sInf {k | ∃ A, IsPat G A ∧ A.rank = k}

/-- Explicit edge tables of T, T^2, T^3 (checked against `spow`). -/
def tab (l : List (ℕ × ℕ)) (i j : Fin 7) : Bool :=
  decide ((i.val, j.val) ∈ l ∨ (j.val, i.val) ∈ l)

def L1 : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(4,6)]
def L2 : List (ℕ × ℕ) := [(0,2),(1,3),(2,4),(3,5),(3,6),(5,6)]
def L3 : List (ℕ × ℕ) :=
  [(0,1),(0,3),(1,2),(1,4),(2,3),(2,5),(2,6),(3,4),(4,5),(4,6)]

theorem spow1 : spow 1 = tab L1 := by
  funext i j; revert i j; decide

theorem spow2 : spow 2 = tab L2 := by
  funext i j; revert i j; decide

theorem spow3 : spow 3 = tab L3 := by
  funext i j; revert i j; decide

theorem not_star : ∀ v : Fin 7, ∃ u, u ≠ v ∧ adjT v u = false := by decide

/-! Lower bounds. -/

theorem rank_ge_of_tri {k : ℕ} (A : Matrix (Fin 7) (Fin 7) ℝ)
    (r c : Fin k → Fin 7) (hU : (A.submatrix r c).IsUpperTriangular)
    (hd : ∀ i, A (r i) (c i) ≠ 0) : k ≤ A.rank := by
  have h1 : ((A.submatrix r c) * 1).rank = (1 : Matrix (Fin k) (Fin k) ℝ).rank :=
    Matrix.rank_mul_eq_right_of_isUpperTriangular _ _ hU (fun i => hd i)
  rw [Matrix.mul_one, Matrix.rank_one, Fintype.card_fin] at h1
  rw [← h1]
  exact Matrix.rank_submatrix_le A r c

theorem zero_of_pat {G : Fin 7 → Fin 7 → Bool} {A : Matrix (Fin 7) (Fin 7) ℝ}
    (h : IsPat G A) {i j : Fin 7} (hij : i ≠ j) (hg : G i j = false) : A i j = 0 := by
  by_contra hne
  have := (h.2 i j hij).1 hne
  simp_all

theorem ne_of_pat {G : Fin 7 → Fin 7 → Bool} {A : Matrix (Fin 7) (Fin 7) ℝ}
    (h : IsPat G A) {i j : Fin 7} (hij : i ≠ j) (hg : G i j = true) : A i j ≠ 0 :=
  (h.2 i j hij).2 hg

theorem lower1 (A : Matrix (Fin 7) (Fin 7) ℝ) (h : IsPat (spow 1) A) : 5 ≤ A.rank := by
  rw [spow1] at h
  apply rank_ge_of_tri A ![1, 2, 3, 4, 5] ![0, 1, 2, 3, 4]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      exact zero_of_pat h (by decide) (by decide)
  · intro i
    fin_cases i <;> simp <;> exact ne_of_pat h (by decide) (by decide)

theorem lower2 (A : Matrix (Fin 7) (Fin 7) ℝ) (h : IsPat (spow 2) A) : 4 ≤ A.rank := by
  rw [spow2] at h
  apply rank_ge_of_tri A ![2, 0, 3, 1] ![4, 2, 5, 3]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      exact zero_of_pat h (by decide) (by decide)
  · intro i
    fin_cases i <;> simp <;> exact ne_of_pat h (by decide) (by decide)

theorem lower3 (A : Matrix (Fin 7) (Fin 7) ℝ) (h : IsPat (spow 3) A) : 4 ≤ A.rank := by
  rw [spow3] at h
  apply rank_ge_of_tri A ![2, 0, 1, 5] ![6, 3, 0, 2]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      exact zero_of_pat h (by decide) (by decide)
  · intro i
    fin_cases i <;> simp <;> exact ne_of_pat h (by decide) (by decide)

/-! Upper bounds: explicit matrices. -/

def U1 : Matrix (Fin 7) (Fin 5) ℝ :=
  !![-1, 1, 0, 0, 0; 1, -1, 1, 0, 0; 0, 1, -1, 1, 0; 0, 0, 1, 0, 1;
     0, 0, 0, 1, -1; 0, 0, 0, 0, 1; 0, 0, 0, 0, 1]
def W1 : Matrix (Fin 5) (Fin 7) ℝ :=
  !![1, 0, 0, 0, 0, -1, -1; 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 0]
def A1 : Matrix (Fin 7) (Fin 7) ℝ :=
  !![-1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0;
     0, 0, 1, 0, 1, 0, 0; 0, 0, 0, 1, -1, 1, 1; 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 0]

/-- Gram vectors for T^2: 0,2,4 in coordinates 0,1; 1,3,5,6 in 2,3. -/
def U2 : Matrix (Fin 7) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 1, 1, 0, 0; 0, 0, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1;
     0, 0, 0, 2]
def A2 : Matrix (Fin 7) (Fin 7) ℝ :=
  !![1, 0, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0; 1, 0, 2, 0, 1, 0, 0;
     0, 1, 0, 2, 0, 1, 2; 0, 0, 1, 0, 1, 0, 0; 0, 0, 0, 1, 0, 1, 2;
     0, 0, 0, 2, 0, 2, 4]

/-- Gram vectors for T^3: 1,3,5,6 the unit vectors, 0,2,4 orthogonal mixes. -/
def U3 : Matrix (Fin 7) (Fin 4) ℝ :=
  !![1, 1, 0, 0; 1, 0, 0, 0; 1, -1, 1, 1; 0, 1, 0, 0; 1, -1, -1, -1;
     0, 0, 1, 0; 0, 0, 0, 1]
def A3 : Matrix (Fin 7) (Fin 7) ℝ :=
  !![2, 1, 0, 1, 0, 0, 0; 1, 1, 1, 0, 1, 0, 0; 0, 1, 4, -1, 0, 1, 1;
     1, 0, -1, 1, -1, 0, 0; 0, 1, 0, -1, 4, -1, -1; 0, 0, 1, 0, -1, 1, 0;
     0, 0, 1, 0, -1, 0, 1]

theorem A1_eq : A1 = U1 * W1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A1, U1, W1, Matrix.mul_apply, Fin.sum_univ_succ]

theorem A2_eq : A2 = U2 * U2.transpose := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A2, U2, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem A3_eq : A3 = U3 * U3.transpose := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A3, U3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem pat1 : IsPat (spow 1) A1 := by
  rw [spow1]
  refine ⟨?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [A1]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [A1, tab, L1]

theorem pat2 : IsPat (spow 2) A2 := by
  rw [spow2]
  refine ⟨?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [A2]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [A2, tab, L2]

theorem pat3 : IsPat (spow 3) A3 := by
  rw [spow3]
  refine ⟨?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [A3]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [A3, tab, L3]

theorem rank_A1 : A1.rank ≤ 5 := by
  rw [A1_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem rank_A2 : A2.rank ≤ 4 := by
  rw [A2_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem rank_A3 : A3.rank ≤ 4 := by
  rw [A3_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem mr_eq {G : Fin 7 → Fin 7 → Bool} {k : ℕ} (A : Matrix (Fin 7) (Fin 7) ℝ)
    (hA : IsPat G A) (hr : A.rank ≤ k) (hlow : ∀ B, IsPat G B → k ≤ B.rank) :
    mr G = k := by
  have hk : A.rank = k := le_antisymm hr (hlow A hA)
  apply le_antisymm
  · exact Nat.sInf_le ⟨A, hA, hk⟩
  · refine le_csInf ⟨k, A, hA, hk⟩ ?_
    rintro m ⟨B, hB, rfl⟩
    exact hlow B hB

/-- Q8 fails for the 7-vertex tree `adjT`: not a star, and
mr(T) = 5, mr(T^2) = 4, mr(T^3) = 4 (no strict decrease from T^2 to T^3,
while the value 4 is above 2). -/
theorem aimmatrix_mr8 :
    (∀ v : Fin 7, ∃ u, u ≠ v ∧ adjT v u = false) ∧
    mr (spow 1) = 5 ∧ mr (spow 2) = 4 ∧ mr (spow 3) = 4 ∧
    ¬ (mr (spow 3) < mr (spow 2)) ∧ 2 < mr (spow 2) :=
  by
  have h1 := mr_eq A1 pat1 rank_A1 lower1
  have h2 := mr_eq A2 pat2 rank_A2 lower2
  have h3 := mr_eq A3 pat3 rank_A3 lower3
  refine ⟨not_star, h1, h2, h3, ?_, ?_⟩ <;> omega

