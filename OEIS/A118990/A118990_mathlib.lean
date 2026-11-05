/-
OEIS A118990 (symmetric singular n x n matrices with entries 1 or -1) and
OEIS A086906 (symmetric singular m x m matrices with entries 0 or 1).

Checked here:
* `A118990_pm m` = the Finset of m x m integer matrices with every entry in {1, -1},
  symmetric, with determinant 0 (its card is A118990(m)).
* `A118990_zo m` = the same with entries in {0, 1} (its card is A086906(m)).
* `A118990_eq` (main): for every n, card (A118990_pm (n+1)) = 2^(n+1) * card (A118990_zo n).
  With the OEIS offsets this is A118990(n) = 2^n * A086906(n-1) for n >= 2.
* `A118990_det_norm`: the determinant identity behind it. The matrix with first row and
  column all ones and lower block 1 - 2B has determinant (-2)^n det B.

The bijection is (s, B) -> M with M i j = s 0 * e i * e j * N i j, where s is a sign vector of
length n+1, e = (1, s 1, ..., s n), and N is the matrix above. Its inverse reads
s 0 = M 0 0, s k = M 0 0 * M 0 k, and B a b = (1 - M 0 0 * M 0 a * M 0 b * M a b) div 2.

The two Finsets use classical decidability, so no `decide` check of small terms is made here.
Not checked in Lean: the values of the terms and the identification of these Finset cards with the OEIS data (the
definitions follow the OEIS names; certificate/check.py compares brute-force counts for
n <= 5 with the OEIS terms).
-/
import Mathlib

open Finset Matrix

open Classical in
/-- Symmetric m x m matrices with entries in {1, -1} and determinant 0 (A118990). -/
noncomputable def A118990_pm (m : ℕ) : Finset (Matrix (Fin m) (Fin m) ℤ) :=
  Finset.filter (fun M : Matrix (Fin m) (Fin m) ℤ => (∀ i j, M i j = M j i) ∧ M.det = 0)
    ((Fintype.piFinset fun _ : Fin m => Fintype.piFinset fun _ : Fin m => ({1, -1} : Finset ℤ)).map
      Matrix.of.toEmbedding)

open Classical in
/-- Symmetric m x m matrices with entries in {0, 1} and determinant 0 (A086906). -/
noncomputable def A118990_zo (m : ℕ) : Finset (Matrix (Fin m) (Fin m) ℤ) :=
  Finset.filter (fun M : Matrix (Fin m) (Fin m) ℤ => (∀ i j, M i j = M j i) ∧ M.det = 0)
    ((Fintype.piFinset fun _ : Fin m => Fintype.piFinset fun _ : Fin m => ({0, 1} : Finset ℤ)).map
      Matrix.of.toEmbedding)

/-- Sign vectors of length m. -/
def A118990_signs (m : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ : Fin m => ({1, -1} : Finset ℤ)

/-- First row and column all ones, lower block 1 - 2B. -/
def A118990_norm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => ℤ) 1
      (fun a => Fin.cases (motive := fun _ => ℤ) 1 (fun b => 1 - 2 * B a b) j) i

/-- The conjugating signs (1, s 1, ..., s n). -/
def A118990_e {n : ℕ} (s : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => Fin.cases (motive := fun _ => ℤ) 1 (fun k => s k.succ) i

/-- (s, B) -> s 0 * diag(e) * N * diag(e). -/
def A118990_fwd {n : ℕ} (p : (Fin (n + 1) → ℤ) × Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => p.1 0 * A118990_e p.1 i * A118990_e p.1 j * A118990_norm p.2 i j

/-- The inverse of `A118990_fwd` on symmetric sign matrices. -/
def A118990_bwd {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    (Fin (n + 1) → ℤ) × Matrix (Fin n) (Fin n) ℤ :=
  (fun i => Fin.cases (motive := fun _ => ℤ) (M 0 0) (fun k => M 0 0 * M 0 k.succ) i,
   Matrix.of fun a b => (1 - M 0 0 * M 0 a.succ * M 0 b.succ * M a.succ b.succ) / 2)

lemma A118990_det_norm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    (A118990_norm B).det = (-2) ^ n * B.det := by
  set N := A118990_norm B
  let c : Fin (n + 1) → ℤ := fun i => Fin.cases (motive := fun _ => ℤ) 0 (fun _ => -1) i
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => N i j + c i * N 0 j
  have hA : A.det = N.det :=
    det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) (fun i j => rfl)
  rw [← hA, det_succ_column_zero, Fin.sum_univ_succ]
  have hsub : A.submatrix (Fin.succAbove 0) Fin.succ = (-2 : ℤ) • B := by
    ext a b
    simp [A, N, c, A118990_norm]
    ring
  have hcol : ∀ k : Fin n, A k.succ 0 = 0 := by
    intro k
    simp [A, N, c, A118990_norm]
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hsub, det_smul,
    Fintype.card_fin]
  simp [A, N, c, A118990_norm]

@[simp] lemma A118990_fwd_00 {n : ℕ} (s : Fin (n + 1) → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) :
    A118990_fwd (s, B) 0 0 = s 0 := by
  simp [A118990_fwd, A118990_e, A118990_norm]

@[simp] lemma A118990_fwd_0s {n : ℕ} (s : Fin (n + 1) → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n) : A118990_fwd (s, B) 0 b.succ = s 0 * s b.succ := by
  simp [A118990_fwd, A118990_e, A118990_norm]

@[simp] lemma A118990_fwd_s0 {n : ℕ} (s : Fin (n + 1) → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (a : Fin n) : A118990_fwd (s, B) a.succ 0 = s 0 * s a.succ := by
  simp [A118990_fwd, A118990_e, A118990_norm]

@[simp] lemma A118990_fwd_ss {n : ℕ} (s : Fin (n + 1) → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (a b : Fin n) :
    A118990_fwd (s, B) a.succ b.succ = s 0 * s a.succ * s b.succ * (1 - 2 * B a b) := by
  simp [A118990_fwd, A118990_e, A118990_norm]

lemma A118990_det_fwd {n : ℕ} (s : Fin (n + 1) → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hs : ∀ i, s i ≠ 0) : (A118990_fwd (s, B)).det = 0 ↔ B.det = 0 := by
  have hM : A118990_fwd (s, B) =
      s 0 • (diagonal (A118990_e s) * A118990_norm B * diagonal (A118990_e s)) := by
    ext i j
    simp [A118990_fwd, diagonal_mul, mul_diagonal]
    ring
  have he : ∀ i, A118990_e s i ≠ 0 := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [A118990_e]
    · simpa [A118990_e] using hs k.succ
  have hp : (∏ i, A118990_e s i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => he i)
  rw [hM, det_smul, det_mul, det_mul, det_diagonal, A118990_det_norm]
  simp [hs 0, hp]

lemma A118990_pm_iff (x : ℤ) : x ∈ ({1, -1} : Finset ℤ) ↔ (x = 1 ∨ x = -1) := by
  simp

lemma A118990_zo_iff (x : ℤ) : x ∈ ({0, 1} : Finset ℤ) ↔ (x = 0 ∨ x = 1) := by
  simp

lemma A118990_mem_pm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) :
    M ∈ A118990_pm m ↔
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧ (∀ i j, M i j = M j i) ∧ M.det = 0 := by
  simp only [A118990_pm, Finset.mem_filter, Finset.mem_map_equiv, Fintype.mem_piFinset, A118990_pm_iff,
    Matrix.of_symm_apply]

lemma A118990_mem_zo {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) :
    M ∈ A118990_zo m ↔
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧ (∀ i j, M i j = M j i) ∧ M.det = 0 := by
  simp only [A118990_zo, Finset.mem_filter, Finset.mem_map_equiv, Fintype.mem_piFinset, A118990_zo_iff,
    Matrix.of_symm_apply]

lemma A118990_mem_signs {m : ℕ} (s : Fin m → ℤ) :
    s ∈ A118990_signs m ↔ ∀ i, s i = 1 ∨ s i = -1 := by
  unfold A118990_signs
  rw [Fintype.mem_piFinset]
  simp only [A118990_pm_iff]

lemma A118990_sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

lemma A118990_sign_sq {a : ℤ} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with ha | ha <;> simp [ha]

/-- `A118990_fwd ∘ A118990_bwd` is the identity on symmetric sign matrices. -/
lemma A118990_fwd_bwd {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) (hsym : ∀ i j, M i j = M j i) :
    A118990_fwd (A118990_bwd M) = M := by
  have h00 := A118990_sign_sq (hM 0 0)
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · simp [A118990_bwd]
  · simp only [A118990_bwd, A118990_fwd_0s, Fin.cases_zero, Fin.cases_succ]
    rw [← mul_assoc, h00, one_mul]
  · simp only [A118990_bwd, A118990_fwd_s0, Fin.cases_zero, Fin.cases_succ]
    rw [← mul_assoc, h00, one_mul, hsym]
  · simp only [A118990_bwd, A118990_fwd_ss, Fin.cases_zero, Fin.cases_succ, Matrix.of_apply]
    have hx := A118990_sign_mul (A118990_sign_mul (A118990_sign_mul (hM 0 0) (hM 0 a.succ))
      (hM 0 b.succ)) (hM a.succ b.succ)
    have hy : 1 - 2 * ((1 - M 0 0 * M 0 a.succ * M 0 b.succ * M a.succ b.succ) / 2) =
        M 0 0 * M 0 a.succ * M 0 b.succ * M a.succ b.succ := by
      generalize M 0 0 * M 0 a.succ * M 0 b.succ * M a.succ b.succ = x at hx ⊢
      omega
    rw [hy]
    have ha := A118990_sign_sq (hM 0 a.succ)
    have hb := A118990_sign_sq (hM 0 b.succ)
    calc M 0 0 * (M 0 0 * M 0 a.succ) * (M 0 0 * M 0 b.succ) *
          (M 0 0 * M 0 a.succ * M 0 b.succ * M a.succ b.succ)
        = (M 0 0 * M 0 0) * (M 0 0 * M 0 0) * (M 0 a.succ * M 0 a.succ) *
            (M 0 b.succ * M 0 b.succ) * M a.succ b.succ := by ring
      _ = M a.succ b.succ := by rw [h00, ha, hb]; ring

/-- `A118990_bwd ∘ A118990_fwd` is the identity when s is a sign vector. -/
lemma A118990_bwd_fwd {n : ℕ} (s : Fin (n + 1) → ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : A118990_bwd (A118990_fwd (s, B)) = (s, B) := by
  have h0 := A118990_sign_sq (hs 0)
  refine Prod.ext ?_ ?_
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [A118990_bwd]
    · simp only [A118990_bwd, A118990_fwd_00, A118990_fwd_0s, Fin.cases_succ]
      rw [← mul_assoc, h0, one_mul]
  · ext a b
    simp only [A118990_bwd, A118990_fwd_00, A118990_fwd_0s, A118990_fwd_ss, Matrix.of_apply]
    have ha := A118990_sign_sq (hs a.succ)
    have hb := A118990_sign_sq (hs b.succ)
    have hk : s 0 * (s 0 * s a.succ) * (s 0 * s b.succ) *
        (s 0 * s a.succ * s b.succ * (1 - 2 * B a b)) = 1 - 2 * B a b := by
      calc s 0 * (s 0 * s a.succ) * (s 0 * s b.succ) *
            (s 0 * s a.succ * s b.succ * (1 - 2 * B a b))
          = (s 0 * s 0) * (s 0 * s 0) * (s a.succ * s a.succ) * (s b.succ * s b.succ) *
              (1 - 2 * B a b) := by ring
        _ = 1 - 2 * B a b := by rw [h0, ha, hb]; ring
    rw [hk]
    omega

/-- A118990(n+1) = 2^(n+1) * A086906(n): the number of singular symmetric (n+1) x (n+1)
matrices with entries ±1 is 2^(n+1) times the number of singular symmetric n x n matrices
with entries 0/1. -/
theorem A118990_eq (n : ℕ) :
    (A118990_pm (n + 1)).card = 2 ^ (n + 1) * (A118990_zo n).card := by
  have h2 : (A118990_signs (n + 1)).card = 2 ^ (n + 1) := by
    simp [A118990_signs]
  rw [← h2, ← Finset.card_product]
  symm
  refine Finset.card_nbij' A118990_fwd A118990_bwd ?_ ?_ ?_ ?_
  · rintro ⟨s, B⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, A118990_mem_signs, A118990_mem_zo] at hp
    obtain ⟨hs, hB, hsym, hdet⟩ := hp
    simp only [Finset.mem_coe, A118990_mem_pm]
    refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · simpa using hs 0
      · simpa using A118990_sign_mul (hs 0) (hs b.succ)
      · simpa using A118990_sign_mul (hs 0) (hs a.succ)
      · have hb : 1 - 2 * B a b = 1 ∨ 1 - 2 * B a b = -1 := by
          rcases hB a b with h | h <;> simp [h]
        simpa using A118990_sign_mul (A118990_sign_mul (A118990_sign_mul (hs 0) (hs a.succ))
          (hs b.succ)) hb
    · refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · rfl
      · simp
      · simp
      · simp only [A118990_fwd_ss]
        rw [hsym a b]
        ring
    · exact (A118990_det_fwd s B (fun i => by rcases hs i with h | h <;> simp [h])).mpr hdet
  · intro M hM
    simp only [Finset.mem_coe, A118990_mem_pm] at hM
    obtain ⟨hM, hsym, hdet⟩ := hM
    have hs : ∀ i, (A118990_bwd M).1 i = 1 ∨ (A118990_bwd M).1 i = -1 := by
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simpa [A118990_bwd] using hM 0 0
      · simpa [A118990_bwd] using A118990_sign_mul (hM 0 0) (hM 0 k.succ)
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, A118990_mem_signs, A118990_mem_zo]
    refine ⟨hs, fun a b => ?_, fun a b => ?_, ?_⟩
    · have hx := A118990_sign_mul (A118990_sign_mul (A118990_sign_mul (hM 0 0) (hM 0 a.succ))
        (hM 0 b.succ)) (hM a.succ b.succ)
      simp only [A118990_bwd, Matrix.of_apply]
      generalize M 0 0 * M 0 a.succ * M 0 b.succ * M a.succ b.succ = x at hx ⊢
      omega
    · simp only [A118990_bwd, Matrix.of_apply]
      rw [hsym a.succ b.succ]
      congr 2
      ring
    · have h := A118990_fwd_bwd M hM hsym
      rw [← h] at hdet
      refine (A118990_det_fwd (A118990_bwd M).1 (A118990_bwd M).2 (fun i h0 => ?_)).mp hdet
      rcases hs i with h | h <;> rw [h] at h0 <;> norm_num at h0
  · rintro ⟨s, B⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, A118990_mem_signs, A118990_mem_zo] at hp
    exact A118990_bwd_fwd s B hp.1
  · intro M hM
    simp only [Finset.mem_coe, A118990_mem_pm] at hM
    exact A118990_fwd_bwd M hM.1 hM.2.1
