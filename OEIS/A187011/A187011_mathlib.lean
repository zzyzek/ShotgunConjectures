/-
OEIS A187011: a(n) = det(|p_i - p_j|)_{1 ≤ i,j ≤ n}, p_k the k-th prime
(offset 0, a(0) = 1).  Conjecture (Zhi-Wei Sun, entry text):
(-1)^(n-1) a(n) > 0 for all n > 1, and |a(n)|^(1/n) tends to infinity.

Definitions.  `distMat n x` is the n × n matrix (|x i - x j|) for
x : ℕ → R, R a linearly ordered commutative ring (ℤ, ℚ, ℝ, ...).
`a n` is `(distMat n p).det` over ℤ with p i = Nat.nth Nat.Prime i
(p 0 = 2, so p i is the (i+1)-st prime).

Main theorems.
* `det_distMat`: for strictly increasing x and n ≥ 2,
  det (|x i - x j|) = (-1)^(n-1) 2^(n-2) (x (n-1) - x 0) ∏_{i<n-1} (x (i+1) - x i)
  (determinant of the distance matrix of a weighted path).
* `A187011_formula`: the same formula for a n with x = primes.
* `A187011_sign`: 2 ≤ n → 0 < (-1)^(n-1) * a n (first half of the conjecture).

Proof.  With U = I - (superdiagonal of ones), U D Uᵀ is the arrowhead matrix
with diagonal -2 d_i (i < n-1), last row and column d_i, corner 0, where
d_i = x (i+1) - x i.  Multiplying on the right by an upper triangular V
with det V = 2 makes it lower triangular with diagonal
-2 d_0, ..., -2 d_{n-2}, x (n-1) - x 0.

Not checked in Lean: the second half of the conjecture, |a(n)|^(1/n) → ∞.
By `A187011_formula` it is equivalent to the geometric mean of the first
n-1 prime gaps tending to infinity, which we derive (README) from a Brun or
Selberg upper bound for prime pairs p, p + h uniform in h; that sieve bound
is not in Mathlib.
-/
import Mathlib

open Matrix Finset

/-- Rewrite an `if` with a false condition. -/
theorem iteF {α : Type*} {c : Prop} [Decidable c] (h : ¬c) (u v : α) : ite c u v = v := by
  simp [h]

/-- Rewrite an `if` with a true condition. -/
theorem iteT {α : Type*} {c : Prop} [Decidable c] (h : c) (u v : α) : ite c u v = u := by
  simp [h]

section General

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The distance matrix (|x i - x j|) of the points x 0, ..., x (n-1). -/
def distMat (n : ℕ) (x : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => |x i - x j|

/-- I minus the superdiagonal of ones (row i ↦ row i - row (i+1)). -/
def shiftU (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i k => (if (k : ℕ) = i then 1 else 0) - (if (k : ℕ) = i + 1 then 1 else 0)

/-- Last column 1, ..., 1, 2; identity elsewhere. -/
def lastColV (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun j l =>
    if (l : ℕ) = m then (if (j : ℕ) = m then 2 else 1) else (if j = l then 1 else 0)

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma sum_ind_mul (n a : ℕ) (g : ℕ → R) :
    ∑ k : Fin n, (if (k : ℕ) = a then (1 : R) else 0) * g k = if a < n then g a else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (if k = a then (1 : R) else 0) * g k) n]
  simp [Finset.sum_ite_eq']

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma sum_mul_ind (n a : ℕ) (g : ℕ → R) :
    ∑ k : Fin n, g k * (if (k : ℕ) = a then (1 : R) else 0) = if a < n then g a else 0 := by
  rw [← sum_ind_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma det_shiftU (n : ℕ) : (shiftU n : Matrix (Fin n) (Fin n) R).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp [shiftU]
  · intro i j hij
    have h : (j : ℕ) < i := hij
    simp only [shiftU, of_apply]
    rw [iteF (by omega), iteF (by omega)]
    simp

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma det_lastColV (m : ℕ) : (lastColV m : Matrix (Fin (m + 1)) (Fin (m + 1)) R).det = 2 := by
  rw [det_of_isUpperTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [lastColV, Fin.val_castSucc, Fin.val_last, Fin.is_lt, ne_of_lt]
  · intro i j hij
    have h : (j : ℕ) < i := hij
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
    simp only [lastColV, of_apply]
    rw [iteF (by omega), iteF (fun e => by rw [e] at h; omega)]

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma shiftU_mul (n : ℕ) (F : ℕ → ℕ → R) :
    shiftU n * (Matrix.of fun i j : Fin n => F i j) =
      Matrix.of fun i j : Fin n => F i j - (if (i : ℕ) + 1 < n then F (i + 1) j else 0) := by
  ext i j
  simp only [mul_apply, shiftU, of_apply, sub_mul, Finset.sum_sub_distrib]
  rw [sum_ind_mul n i (fun k => F k j), sum_ind_mul n (i + 1) (fun k => F k j), iteT i.is_lt]

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma mul_shiftU_transpose (n : ℕ) (F : ℕ → ℕ → R) :
    (Matrix.of fun i j : Fin n => F i j) * (shiftU n)ᵀ =
      Matrix.of fun i j : Fin n => F i j - (if (j : ℕ) + 1 < n then F i (j + 1) else 0) := by
  ext i j
  simp only [mul_apply, shiftU, of_apply, transpose_apply, mul_sub, Finset.sum_sub_distrib]
  rw [sum_mul_ind n j (fun k => F i k), sum_mul_ind n (j + 1) (fun k => F i k), iteT j.is_lt]

lemma abs_sub_mono {x : ℕ → R} (hx : Monotone x) (a b : ℕ) :
    |x a - x b| = if a ≤ b then x b - x a else x a - x b := by
  split_ifs with h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hx h))]
  · exact abs_of_nonneg (sub_nonneg.mpr (hx (by omega)))

/-- Entries of U D Uᵀ: the arrowhead matrix. -/
lemma arrow_entry {x : ℕ → R} (hx : Monotone x) (m i j : ℕ) (hi : i ≤ m) (hj : j ≤ m) :
    (|x i - x j| - (if i + 1 < m + 1 then |x (i + 1) - x j| else 0)) -
      (if j + 1 < m + 1 then
        |x i - x (j + 1)| - (if i + 1 < m + 1 then |x (i + 1) - x (j + 1)| else 0) else 0) =
      if i < m then
        (if j < m then (if i = j then -2 * (x (i + 1) - x i) else 0) else x (i + 1) - x i)
      else (if j < m then x (j + 1) - x j else 0) := by
  simp only [abs_sub_mono hx]
  split_ifs <;>
    first
    | omega
    | ring1
    | ((obtain rfl : i = j := by omega); ring1)
    | ((obtain rfl : i = j + 1 := by omega); ring1)

/-- The determinant of the distance matrix of a weighted path. -/
theorem det_distMat {x : ℕ → R} (hx : StrictMono x) (n : ℕ) (hn : 2 ≤ n) :
    (distMat n x).det =
      (-1) ^ (n - 1) * 2 ^ (n - 2) * (x (n - 1) - x 0) *
        ∏ i ∈ range (n - 1), (x (i + 1) - x i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmono := hx.monotone
  set D := distMat (m + 1) x
  -- C = U D Uᵀ, then C V is lower triangular.
  --
  have hC : shiftU (m + 1) * D * (shiftU (m + 1))ᵀ = Matrix.of fun i j : Fin (m + 1) =>
      if (i : ℕ) < m then
        (if (j : ℕ) < m then (if (i : ℕ) = j then -2 * (x (i + 1) - x i) else 0)
          else x (i + 1) - x i)
      else (if (j : ℕ) < m then x (j + 1) - x j else 0) := by
    have hD : D = Matrix.of fun i j : Fin (m + 1) => |x i - x j| := rfl
    rw [hD, shiftU_mul (m + 1) (fun a b => |x a - x b|),
      mul_shiftU_transpose (m + 1)
        (fun a b => |x a - x b| - (if a + 1 < m + 1 then |x (a + 1) - x b| else 0))]
    ext i j
    simp only [of_apply]
    exact arrow_entry hmono m i j (Nat.lt_succ_iff.mp i.is_lt) (Nat.lt_succ_iff.mp j.is_lt)
  set C := shiftU (m + 1) * D * (shiftU (m + 1))ᵀ with hCdef
  -- Row sums of C over the first m columns.
  --
  have hrow : ∀ i : Fin (m + 1), ∑ j : Fin m, C i j.castSucc =
      if (i : ℕ) < m then -2 * (x (i + 1) - x i) else x m - x 0 := by
    intro i
    rw [hC]
    simp only [of_apply, Fin.val_castSucc, Fin.is_lt, ite_true]
    split_ifs with hi
    · rw [Fintype.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro j hj
        rw [iteF]
        intro e
        exact hj (Fin.ext e.symm)
    · rw [Fin.sum_univ_eq_sum_range (fun j => x (j + 1) - x j) m]
      exact Finset.sum_range_sub x m
  have hCV : (C * (lastColV m : Matrix (Fin (m + 1)) (Fin (m + 1)) R)).det =
      (∏ i : Fin m, (-2 * (x (i + 1) - x i))) * (x m - x 0) := by
    have hent : ∀ i l : Fin (m + 1), (C * (lastColV m : Matrix (Fin (m + 1)) (Fin (m + 1)) R)) i l =
        if (l : ℕ) = m then (∑ j : Fin m, C i j.castSucc) + 2 * C i (Fin.last m)
        else C i l := by
      intro i l
      rw [mul_apply, Fin.sum_univ_castSucc]
      by_cases hl : (l : ℕ) = m
      · have hl' : l = Fin.last m := Fin.ext (by simp [hl])
        subst hl'
        have : ∀ j : Fin m, ((j : ℕ) = m) = False := fun j => by simp [j.is_lt.ne]
        simp [lastColV, this, mul_comm]
      · obtain ⟨k, rfl⟩ : ∃ k : Fin m, k.castSucc = l :=
          Fin.exists_castSucc_eq.mpr (fun e => hl (by simp [e]))
        have hk : (k : ℕ) ≠ m := k.is_lt.ne
        simp [lastColV, hk, Fin.castSucc_inj, (Fin.castSucc_lt_last k).ne']
    have hlast : ∀ i : Fin (m + 1), C i (Fin.last m) =
        if (i : ℕ) < m then x (i + 1) - x i else 0 := by
      intro i
      rw [hC]
      simp [Fin.val_last]
    rw [det_of_isLowerTriangular]
    · rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hent, iteF (by simp [i.is_lt.ne]), hC]
        simp [i.is_lt]
      · rw [hent, iteT (by simp), hrow, hlast]
        simp
    · intro i l hil
      have h : (i : ℕ) < l := hil
      rw [hent]
      split_ifs with hl
      · rw [hrow, hlast, iteT (by omega), iteT (by omega)]
        ring
      · rw [hC]
        simp only [of_apply]
        rw [iteT (by omega), iteT (by omega), iteF (by omega)]
  -- det C = det D, and det (C V) = 2 det C.
  --
  have hdet : (C * (lastColV m : Matrix (Fin (m + 1)) (Fin (m + 1)) R)).det = D.det * 2 := by
    rw [det_mul, hCdef, det_mul, det_mul, det_transpose, det_shiftU, det_lastColV]
    ring
  rw [hdet, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun i => x (i + 1) - x i) m] at hCV
  have h2 : (2 : R) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have key : D.det * 2 =
      ((-1) ^ m * 2 ^ (m - 1) * (x m - x 0) * ∏ i ∈ range m, (x (i + 1) - x i)) * 2 := by
    rw [hCV, show (-2 : R) = (-1) * 2 by ring, mul_pow, h2]
    ring
  have h2ne : (2 : R) ≠ 0 := two_ne_zero
  simpa [Nat.add_sub_cancel] using mul_right_cancel₀ h2ne key

end General

/-- The k-th prime, counted from 0 (`p 0 = 2`). -/
noncomputable def p (i : ℕ) : ℤ := (Nat.nth Nat.Prime i : ℤ)

lemma p_strictMono : StrictMono p := by
  intro a b h
  simp only [p, Nat.cast_lt]
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime h

/-- A187011(n) = det (|p_i - p_j|) over the first n primes. -/
noncomputable def a (n : ℕ) : ℤ := (distMat n p).det

theorem A187011_formula (n : ℕ) (hn : 2 ≤ n) :
    a n = (-1) ^ (n - 1) * 2 ^ (n - 2) * (p (n - 1) - p 0) *
      ∏ i ∈ range (n - 1), (p (i + 1) - p i) :=
  det_distMat p_strictMono n hn

theorem A187011_sign (n : ℕ) (hn : 2 ≤ n) : 0 < (-1) ^ (n - 1) * a n := by
  rw [A187011_formula n hn, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  apply mul_pos
  · apply mul_pos
    · positivity
    · exact sub_pos.mpr (p_strictMono (by omega))
  · exact Finset.prod_pos (fun i _ => sub_pos.mpr (p_strictMono (Nat.lt_succ_self i)))
