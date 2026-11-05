/-
OEIS A054120 (record OEIS-A054120b), Mathlib proof of G. McGarvey's second conjecture
  T(n,k) = A081577(n,k) - A081577(n-2,k-1),
with A081577 read as a triangle (row n, position k) and taken as 0 outside 0 ≤ k ≤ n.

Definitions, as in the entries.
* `A054120 n k`: T(n,0) = T(n,n) = 1, T(n,k) = 0 for k > n, and for 0 < k < n
  T(n,k) = Σ T(i,j) over i < n, j ≤ i with T(i,j) on or between the vertical lines through
  T(n-1,k-1) and T(n-1,k). In the centred layout T(i,j) sits at horizontal position 2j - i, so
  the condition is 2k - n - 1 ≤ 2j - i ≤ 2k - n + 1 (rows i < n are the entries "not below" T(n,k),
  other than T(n,k) itself).
* `A081577_sq a b`: the Pascal-(1,2,1) square array, S(a,0) = S(0,b) = 1,
  S(a,b) = S(a,b-1) + 2 S(a-1,b-1) + S(a-1,b). `A081577 n k` = S(n-k, k) for k ≤ n, else 0
  (the antidiagonal reading; the array is symmetric, `A081577_sq_symm`).

Main theorem `A054120b_conjecture`: for all n, k (for k > n both sides are 0),
  T(n,k) = A081577(n,k) - (A081577(n-2,k-1) if n ≥ 2 and k ≥ 1, else 0).

Proof. Let G(n, x) = Σ_{i<n} Σ_{j ≤ i, 2j-i = x} T(i,j) (one vertical line). For n ≥ 1 and all k,
T(n,k) = G(n, 2k-n-1) + G(n, 2k-n) + G(n, 2k-n+1) (`A054120_eq_F`; the boundary cases k = 0, k = n,
k > n are checked separately). T(n,k) and T(n-2,k-1) use the same three lines, and the two rows
n-1, n-2 contribute T(n-1,k-1) + T(n-2,k-1) + T(n-1,k). This is Hendel's proof of McGarvey's first
conjecture T(n,k) = T(n-1,k-1) + 2T(n-2,k-1) + T(n-1,k) (n ≥ 3, k ≥ 1; `A054120_rec`).
The zero-extended triangle A081577 satisfies the same recurrence at every (n,k) ≠ (0,0)
(`A081577z_rec`), so D(n,k) = A081577(n,k) - A081577(n-2,k-1) satisfies it except at (0,0), (2,1).
T and D agree on rows 0, 1, 2 and then by induction on n (`A054120b_main`).
`A054120b_data`: rows 0..7 of D against the entry (via the computable array).

Not checked in Lean: the reading of the geometric definition stated above.
-/
import Mathlib

open Finset

/-- A054120: the triangle defined by sums between vertical lines. -/
def A054120 (n k : ℕ) : ℕ :=
  if k = 0 ∨ k = n then 1 else if n < k then 0 else
    ∑ i ∈ (range n).attach, ∑ j ∈ range (i.1 + 1),
      if 2 * (k : ℤ) - n - 1 ≤ 2 * (j : ℤ) - i.1 ∧ 2 * (j : ℤ) - i.1 ≤ 2 * (k : ℤ) - n + 1 then
        A054120 i.1 j else 0
termination_by n
decreasing_by exact mem_range.mp i.2

theorem A054120_zero (n : ℕ) : A054120 n 0 = 1 := by
  rw [A054120]; simp

theorem A054120_diag (n : ℕ) : A054120 n n = 1 := by
  rw [A054120]; simp

theorem A054120_gt (n k : ℕ) (h : n < k) : A054120 n k = 0 := by
  rw [A054120, ite_eq_right (by omega), ite_eq_left h]

/-- Contribution of row i on the vertical line at position x. -/
noncomputable def A054120_row (i : ℕ) (x : ℤ) : ℤ :=
  ∑ j ∈ range (i + 1), if 2 * (j : ℤ) - i = x then (A054120 i j : ℤ) else 0

/-- Sum of the rows i < n on the vertical line at position x. -/
noncomputable def A054120_G (n : ℕ) (x : ℤ) : ℤ := ∑ i ∈ range n, A054120_row i x

theorem A054120_row_none (i : ℕ) (x : ℤ) (h : ∀ j : ℕ, j ≤ i → 2 * (j : ℤ) - i ≠ x) :
    A054120_row i x = 0 := by
  refine sum_eq_zero fun j hj => ?_
  rw [mem_range] at hj
  rw [ite_eq_right (h j (by omega))]

theorem A054120_row_at (i j : ℕ) (x : ℤ) (hx : x = 2 * (j : ℤ) - i) :
    A054120_row i x = A054120 i j := by
  subst hx
  by_cases hj : j ≤ i
  · unfold A054120_row
    rw [sum_eq_single j]
    · simp
    · intro b _ hb
      rw [ite_eq_right (by omega)]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  · rw [A054120_gt i j (by omega), A054120_row_none]
    · simp
    · intro j' hj'
      omega

theorem A054120_row_odd (i : ℕ) (x : ℤ) (t : ℤ) (h : x + i = 2 * t + 1) : A054120_row i x = 0 :=
  A054120_row_none i x fun j _ => by omega

theorem A054120_G_succ (n : ℕ) (x : ℤ) : A054120_G (n + 1) x = A054120_G n x + A054120_row n x := by
  unfold A054120_G
  rw [sum_range_succ]

theorem A054120_G_none (n : ℕ) (x : ℤ) (h : ∀ i j : ℕ, j ≤ i → i < n → 2 * (j : ℤ) - i ≠ x) :
    A054120_G n x = 0 :=
  sum_eq_zero fun i hi => A054120_row_none i x fun j hj => h i j hj (mem_range.mp hi)

/-- The three vertical lines through T(n-1,k-1), (between), T(n-1,k). -/
noncomputable def A054120_F (n k : ℕ) : ℤ :=
  A054120_G n (2 * k - n - 1) + A054120_G n (2 * k - n) + A054120_G n (2 * k - n + 1)

theorem A054120_interior (n k : ℕ) (h0 : 0 < k) (hn : k < n) : (A054120 n k : ℤ) = A054120_F n k := by
  rw [A054120, ite_eq_right (by omega), ite_eq_right (by omega)]
  push_cast
  rw [sum_attach (range n) (fun i => ∑ j ∈ range (i + 1),
      if 2 * (k : ℤ) - n - 1 ≤ 2 * (j : ℤ) - i ∧ 2 * (j : ℤ) - i ≤ 2 * (k : ℤ) - n + 1 then
        (A054120 i j : ℤ) else 0)]
  unfold A054120_F A054120_G A054120_row
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> omega

theorem A054120_eq_F (n k : ℕ) (hn : 1 ≤ n) : (A054120 n k : ℤ) = A054120_F n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold A054120_F
  rcases Nat.lt_trichotomy k (m + 1) with h | h | h
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [A054120_zero, A054120_G_none, A054120_G_none, A054120_G_succ, A054120_G_none,
        A054120_row_at m 0 _ (by push_cast; ring), A054120_zero]
      · simp
      all_goals intro i j _ hi; push_cast; omega
    · exact A054120_interior (m + 1) k h0 h
  · subst h
    rw [A054120_diag, A054120_G_succ, A054120_G_none, A054120_row_at m m _ (by push_cast; ring),
      A054120_diag, A054120_G_none, A054120_G_none]
    · simp
    all_goals intro i j hji hi; push_cast; omega
  · rw [A054120_gt _ _ h, A054120_G_none, A054120_G_none, A054120_G_none]
    · simp
    all_goals intro i j hji hi; push_cast; omega

/-- Hendel's proof of McGarvey's first conjecture (n ≥ 3, k ≥ 1). -/
theorem A054120_rec (p q : ℕ) (hp : 1 ≤ p) :
    (A054120 (p + 2) (q + 1) : ℤ) =
      A054120 (p + 1) q + 2 * A054120 p q + A054120 (p + 1) (q + 1) := by
  have h1 := A054120_eq_F (p + 2) (q + 1) (by omega)
  have h2 := A054120_eq_F p q hp
  unfold A054120_F at h1 h2
  rw [A054120_G_succ, A054120_G_succ, A054120_G_succ, A054120_G_succ, A054120_G_succ,
    A054120_G_succ] at h1
  have e1 : (2 * ((q + 1 : ℕ) : ℤ) - ((p + 2 : ℕ) : ℤ)) = 2 * (q : ℤ) - p := by push_cast; ring
  rw [e1] at h1
  rw [A054120_row_odd p (2 * q - p - 1) (q - 1) (by ring),
    A054120_row_odd p (2 * q - p + 1) q (by ring),
    A054120_row_odd (p + 1) (2 * q - p) q (by push_cast; ring),
    A054120_row_at p q (2 * q - p) rfl,
    A054120_row_at (p + 1) q (2 * q - p - 1) (by push_cast; ring),
    A054120_row_at (p + 1) (q + 1) (2 * q - p + 1) (by push_cast; ring)] at h1
  linear_combination h1 - h2

/-- One row of the square array from the previous one:
r(0) = 1, r(b+1) = r(b) + 2 prev(b) + prev(b+1). -/
def A081577_next (prev : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | b + 1 => A081577_next prev b + 2 * prev b + prev (b + 1)

/-- The Pascal-(1,2,1) square array A081577: S(a,0) = S(0,b) = 1,
S(a,b) = S(a,b-1) + 2 S(a-1,b-1) + S(a-1,b). -/
def A081577_sq : ℕ → ℕ → ℕ
  | 0, _ => 1
  | a + 1, b => A081577_next (A081577_sq a) b

@[simp]
theorem A081577_sq_zero_left (b : ℕ) : A081577_sq 0 b = 1 := rfl

@[simp]
theorem A081577_sq_zero (a : ℕ) : A081577_sq a 0 = 1 := by
  cases a <;> rfl

theorem A081577_sq_succ (a b : ℕ) :
    A081577_sq (a + 1) (b + 1) = A081577_sq (a + 1) b + 2 * A081577_sq a b + A081577_sq a (b + 1) := rfl

theorem A081577_sq_symm (a b : ℕ) : A081577_sq a b = A081577_sq b a := by
  induction a generalizing b with
  | zero => simp
  | succ a iha =>
    induction b with
    | zero => simp
    | succ b ihb =>
      rw [A081577_sq_succ, A081577_sq_succ, ihb, iha b, iha (b + 1)]
      ring

/-- A081577 as a triangle: row n, position k. -/
def A081577 (n k : ℕ) : ℕ := if k ≤ n then A081577_sq (n - k) k else 0

/-- Zero-extended triangle on ℤ × ℤ. -/
def A081577z (n k : ℤ) : ℤ := if 0 ≤ k ∧ k ≤ n then (A081577_sq (n - k).toNat k.toNat : ℤ) else 0

theorem A081577z_nat (n k : ℕ) : A081577z n k = A081577 n k := by
  unfold A081577z A081577
  by_cases h : k ≤ n
  · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left h]
    congr 2
    omega
  · rw [ite_eq_right (by omega), ite_eq_right h]
    simp

theorem A081577z_eq (n k : ℤ) (a b : ℕ) (h1 : n - k = a) (h2 : k = b) :
    A081577z n k = A081577_sq a b := by
  unfold A081577z
  rw [ite_eq_left ⟨by omega, by omega⟩, h1, h2, Int.toNat_natCast, Int.toNat_natCast]

theorem A081577z_out (n k : ℤ) (h : k < 0 ∨ n < k) : A081577z n k = 0 := by
  unfold A081577z
  rw [ite_eq_right (by omega)]

theorem A081577z_rec (n k : ℤ) (h : ¬ (n = 0 ∧ k = 0)) :
    A081577z n k = A081577z (n - 1) (k - 1) + 2 * A081577z (n - 2) (k - 1) + A081577z (n - 1) k := by
  by_cases hout : k < 0 ∨ n < k
  · rw [A081577z_out n k hout, A081577z_out (n - 1) (k - 1) (by omega),
      A081577z_out (n - 2) (k - 1) (by omega), A081577z_out (n - 1) k (by omega)]
    ring
  rcases eq_or_lt_of_le (show 0 ≤ k by omega) with h0 | h0
  · subst h0
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, n = (a + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
    rw [A081577z_eq ((a + 1 : ℕ) : ℤ) 0 (a + 1) 0 (by simp) (by simp),
      A081577z_out (((a + 1 : ℕ) : ℤ) - 1) (0 - 1) (by omega),
      A081577z_out (((a + 1 : ℕ) : ℤ) - 2) (0 - 1) (by omega),
      A081577z_eq (((a + 1 : ℕ) : ℤ) - 1) 0 a 0 (by push_cast; ring) (by simp),
      A081577_sq_zero, A081577_sq_zero]
    ring
  rcases eq_or_lt_of_le (show k ≤ n by omega) with hn | hn
  · subst hn
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, k = (b + 1 : ℕ) := ⟨(k - 1).toNat, by omega⟩
    rw [A081577z_eq ((b + 1 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ) 0 (b + 1) (by simp) rfl,
      A081577z_out (((b + 1 : ℕ) : ℤ) - 2) (((b + 1 : ℕ) : ℤ) - 1) (by omega),
      A081577z_out (((b + 1 : ℕ) : ℤ) - 1) ((b + 1 : ℕ) : ℤ) (by omega),
      A081577z_eq (((b + 1 : ℕ) : ℤ) - 1) (((b + 1 : ℕ) : ℤ) - 1) 0 b (by simp) (by push_cast; ring)]
    simp
  obtain ⟨b, hb⟩ : ∃ b : ℕ, k = (b + 1 : ℕ) := ⟨(k - 1).toNat, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, n - k = (a + 1 : ℕ) := ⟨(n - k - 1).toNat, by omega⟩
  push_cast at ha hb
  rw [A081577z_eq n k (a + 1) (b + 1) (by push_cast; omega) (by push_cast; omega),
    A081577z_eq (n - 1) (k - 1) (a + 1) b (by push_cast; omega) (by omega),
    A081577z_eq (n - 2) (k - 1) a b (by omega) (by omega),
    A081577z_eq (n - 1) k a (b + 1) (by omega) (by push_cast; omega)]
  rw [A081577_sq_succ]
  push_cast
  ring

/-- T on ℤ × ℤ, zero for negative indices (and, by definition, for k > n). -/
def A054120z (n k : ℤ) : ℤ := if 0 ≤ n ∧ 0 ≤ k then (A054120 n.toNat k.toNat : ℤ) else 0

theorem A054120z_nat (n k : ℕ) : A054120z n k = A054120 n k := by
  simp [A054120z]

theorem A054120z_eq (n k : ℤ) (a b : ℕ) (h1 : n = a) (h2 : k = b) :
    A054120z n k = A054120 a b := by
  rw [h1, h2, A054120z_nat]

theorem A054120z_neg (n k : ℤ) (h : k < 0) : A054120z n k = 0 := by
  unfold A054120z
  rw [ite_eq_right (by omega)]

theorem A054120z_rec (n k : ℤ) (hn : 3 ≤ n) :
    A054120z n k = A054120z (n - 1) (k - 1) + 2 * A054120z (n - 2) (k - 1) + A054120z (n - 1) k := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, n = ((p + 2 : ℕ) : ℤ) := ⟨(n - 2).toNat, by omega⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [A054120z_neg n k hk, A054120z_neg (n - 1) (k - 1) (by omega),
      A054120z_neg (n - 2) (k - 1) (by omega), A054120z_neg (n - 1) k hk]
    ring
  rcases eq_or_lt_of_le hk with hk0 | hk0
  · rw [A054120z_eq n k (p + 2) 0 hp hk0.symm, A054120z_neg (n - 1) (k - 1) (by omega),
      A054120z_neg (n - 2) (k - 1) (by omega),
      A054120z_eq (n - 1) k (p + 1) 0 (by push_cast at hp ⊢; omega) hk0.symm,
      A054120_zero, A054120_zero]
    ring
  obtain ⟨q, hq⟩ : ∃ q : ℕ, k = ((q + 1 : ℕ) : ℤ) := ⟨(k - 1).toNat, by omega⟩
  push_cast at hp hq
  rw [A054120z_eq n k (p + 2) (q + 1) (by push_cast; omega) (by push_cast; omega),
    A054120z_eq (n - 1) (k - 1) (p + 1) q (by push_cast; omega) (by omega),
    A054120z_eq (n - 2) (k - 1) p q (by omega) (by omega),
    A054120z_eq (n - 1) k (p + 1) (q + 1) (by push_cast; omega) (by push_cast; omega)]
  exact A054120_rec p q (by omega)

/-- D(n,k) = A081577(n,k) - A081577(n-2,k-1), zero-extended. -/
def A054120b_D (n k : ℤ) : ℤ := A081577z n k - A081577z (n - 2) (k - 1)

theorem A054120b_D_rec (n k : ℤ) (h0 : ¬ (n = 0 ∧ k = 0)) (h2 : ¬ (n = 2 ∧ k = 1)) :
    A054120b_D n k = A054120b_D (n - 1) (k - 1) + 2 * A054120b_D (n - 2) (k - 1) + A054120b_D (n - 1) k := by
  unfold A054120b_D
  rw [A081577z_rec n k h0, A081577z_rec (n - 2) (k - 1) (by omega)]
  rw [show n - 2 - 1 = n - 1 - 2 by ring, show k - 1 - 1 = k - 1 - 1 by ring,
    show n - 2 - 2 = n - 2 - 2 by ring]
  ring

theorem A054120_two_one : A054120 2 1 = 3 := by
  have h := A054120_interior 2 1 (by omega) (by omega)
  unfold A054120_F at h
  simp only [A054120_G_succ, show A054120_G 0 = fun _ => 0 from rfl] at h
  rw [A054120_row_odd 0 (2 * ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) - 1) (-1) (by norm_num),
    A054120_row_at 1 0 (2 * ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) - 1) (by norm_num),
    A054120_row_at 0 0 (2 * ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) (by norm_num),
    A054120_row_odd 1 (2 * ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) 0 (by norm_num),
    A054120_row_odd 0 (2 * ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) + 1) 0 (by norm_num),
    A054120_row_at 1 1 (2 * ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) + 1) (by norm_num),
    A054120_zero, A054120_zero, A054120_diag] at h
  omega

theorem A054120b_main (n : ℕ) : ∀ k : ℤ, A054120z n k = A054120b_D n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    by_cases hn : 3 ≤ n
    · rw [A054120z_rec n k (by omega), A054120b_D_rec n k (by omega) (by omega),
        show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega, show (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) by omega,
        ih (n - 1) (by omega), ih (n - 2) (by omega), ih (n - 1) (by omega)]
    · have hn3 : n < 3 := by omega
      unfold A054120b_D
      rcases lt_or_ge k 0 with hk | hk
      · rw [A054120z_neg _ _ hk, A081577z_out _ k (Or.inl hk),
          A081577z_out ((n : ℤ) - 2) (k - 1) (Or.inl (by omega))]
        ring
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) := ⟨k.toNat, by omega⟩
      rw [A054120z_nat]
      rcases lt_or_ge n j with hj | hj
      · rw [A054120_gt n j hj, A081577z_out _ _ (Or.inr (by omega)),
          A081577z_out ((n : ℤ) - 2) ((j : ℤ) - 1) (Or.inr (by omega))]
        simp
      interval_cases n <;> interval_cases j
      all_goals simp [A081577z, A081577_sq_succ, A054120_zero, A054120_diag, A054120_two_one]

theorem A054120b_conjecture (n k : ℕ) :
    (A054120 n k : ℤ) =
      A081577 n k - (if 2 ≤ n ∧ 1 ≤ k then (A081577 (n - 2) (k - 1) : ℤ) else 0) := by
  rw [← A054120z_nat, A054120b_main, A054120b_D, A081577z_nat]
  by_cases h : 2 ≤ n ∧ 1 ≤ k
  · rw [ite_eq_left h, show (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) by omega,
      show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, A081577z_nat]
  · rw [ite_eq_right h]
    simp only [sub_zero, sub_eq_self]
    unfold A081577z
    rw [ite_eq_right (by omega)]

theorem A054120b_data :
    ((List.range 8).map fun n => (List.range (n + 1)).map fun k =>
      (A081577 n k : ℤ) - (if 2 ≤ n ∧ 1 ≤ k then (A081577 (n - 2) (k - 1) : ℤ) else 0)) =
    [[1], [1, 1], [1, 3, 1], [1, 6, 6, 1], [1, 9, 18, 9, 1], [1, 12, 39, 39, 12, 1],
      [1, 15, 69, 114, 69, 15, 1], [1, 18, 108, 261, 261, 108, 18, 1]] := by
  decide
