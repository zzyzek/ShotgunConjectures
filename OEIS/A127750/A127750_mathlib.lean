import Mathlib

/-
OEIS A127749 / A127750 (Paul Barry, 2007).
A127749 = inverse of the number triangle A(n,k) = 1/(2n+1) if k <= n <= 2k, 0 otherwise;
A127750 = its row sums.
Conjectures: (1) A127750(n) mod 2 = A036987(n) (1 if n = 2^m - 1, else 0);
(2) row sums of A127749 taken mod 2 entrywise are A111982 (row sums of |A111967|, A111967 the
inverse of the 0/1 triangle A101688(n,k) = [k <= n <= 2k]).

Definitions.
* `B n k` (ℚ): the triangle A(n,k) above. `M n k` (ℤ): A101688 as a triangle.
* `t n k` (ℤ): explicit column recursion; `t_inverse` proves ∑_{j<=n} M n j * t j k = [n = k],
  so `t` is A111967 (`t_unique`: the only such lower-triangular inverse).
* `T n k = (2k+1) * t n k` (A127749): `T_inverse` proves ∑_{j<=n} B n j * T j k = [n = k] and
  `T_unique` that any S with this property equals T.
* `A127750 n = ∑_{k<=n} T n k`; `A036987 n = if ∃ m, n + 1 = 2^m then 1 else 0`;
  `A111982 n = ∑_{k<=n} |t n k|`.

Main theorems.
* `A127750_mod_two`: A127750 n % 2 = A036987 n (conjecture (1)).
* `A127749_rowsum_mod_two`: ∑_{k<=n} (T n k % 2) = A111982 n (conjecture (2)).
* also `rowsum_t` (A111967 row sums = A036987, the A111967 conjecture) and `t_values`
  (every entry of A111967 is -1, 0 or 1).
Not checked: nothing beyond reading the OEIS definitions as above.
-/

def M (n k : ℕ) : ℤ := if k ≤ n ∧ n ≤ 2 * k then 1 else 0

noncomputable def B (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (2 * n + 1) else 0

def t : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => (if n + 1 = k then 1 else 0) - (if n = k then 1 else 0) +
      (if n % 2 = 0 then t (n / 2) k else 0)
decreasing_by omega

def T (n k : ℕ) : ℤ := (2 * k + 1) * t n k

def A127750 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

open Classical in
noncomputable def A036987 (n : ℕ) : ℤ := if ∃ m, n + 1 = 2 ^ m then 1 else 0

lemma ite_pos' {c : Prop} [Decidable c] (h : c) (a b : ℤ) : (if c then a else b) = a := by
  simp [h]

lemma ite_neg' {c : Prop} [Decidable c] (h : ¬ c) (a b : ℤ) : (if c then a else b) = b := by
  simp [h]

def A111982 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), |t n k|

lemma t_succ (n k : ℕ) : t (n + 1) k = (if n + 1 = k then 1 else 0) - (if n = k then 1 else 0) +
    (if n % 2 = 0 then t (n / 2) k else 0) := by
  rw [t]

lemma t_zero (k : ℕ) : t 0 k = if k = 0 then 1 else 0 := by rw [t]

/-- lower triangular -/
lemma t_lower : ∀ n k, n < k → t n k = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    cases n with
    | zero => rw [t_zero]; simp; omega
    | succ n =>
      rw [t_succ]
      have h1 : ¬ (n + 1 = k) := by omega
      have h2 : ¬ (n = k) := by omega
      have h3 : t (n / 2) k = 0 := ih (n / 2) (by omega) k (by omega)
      simp [h1, h2, h3]

/-- prefix sums of a column -/
def S (k m : ℕ) : ℤ := ∑ j ∈ Finset.range m, t j k

lemma window (k : ℕ) : ∀ n, S k (n + 1) - S k ((n + 1) / 2) = if n = k then 1 else 0 := by
  intro n
  induction n with
  | zero => simp [S, t_zero]; omega
  | succ n ih =>
    have hS : S k (n + 2) = S k (n + 1) + t (n + 1) k := by
      simp [S, Finset.sum_range_succ]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have e1 : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have e2 : (n + 1) / 2 = n / 2 := by omega
      have hS2 : S k ((n + 1) / 2 + 1) = S k ((n + 1) / 2) + t (n / 2) k := by
        simp [S, Finset.sum_range_succ, e2]
      rw [e1, hS2, hS, t_succ]
      simp only [h, ite_true]
      split_ifs at ih ⊢ <;> omega
    · have e1 : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      rw [e1, hS, t_succ]
      have h' : ¬ (n % 2 = 0) := by omega
      simp only [h', ite_false]
      split_ifs at ih ⊢ <;> omega

lemma sum_ite_ge (f : ℕ → ℤ) (c m : ℕ) (hc : c ≤ m) :
    ∑ j ∈ Finset.range m, (if c ≤ j then f j else 0) =
      ∑ j ∈ Finset.range m, f j - ∑ j ∈ Finset.range c, f j := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_range_add_sum_Ico f hc]
  have : (Finset.range m).filter (fun j => c ≤ j) = Finset.Ico c m := by
    ext j; simp [Finset.mem_Ico]; omega
  rw [this]; ring

/-- `t` is a (left) inverse of A101688. -/
theorem t_inverse (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), M n j * t j k = if n = k then 1 else 0 := by
  have : ∀ j ∈ Finset.range (n + 1), M n j * t j k = if (n + 1) / 2 ≤ j then t j k else 0 := by
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [M]
    by_cases h : (n + 1) / 2 ≤ j
    · have h' : j ≤ n ∧ n ≤ 2 * j := by omega
      simp [h', h]
    · have h' : ¬ (j ≤ n ∧ n ≤ 2 * j) := by omega
      simp [h', h]
  rw [Finset.sum_congr rfl this, sum_ite_ge _ _ _ (by omega)]
  exact window k n

/-- A127749 = (2k+1) * A111967 is the inverse of A(n,k) = [k <= n <= 2k]/(2n+1). -/
theorem T_inverse (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), B n j * (T j k : ℚ) = if n = k then 1 else 0 := by
  have h : ∀ j ∈ Finset.range (n + 1),
      B n j * (T j k : ℚ) = ((2 * k + 1 : ℚ) / (2 * n + 1)) * ((M n j * t j k : ℤ) : ℚ) := by
    intro j _
    simp only [B, M, T]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← Int.cast_sum, t_inverse]
  split_ifs with hnk
  · subst hnk; push_cast
    have : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  · simp

/-- Uniqueness of the inverse (so `T` is A127749 as the entry defines it). -/
theorem T_unique (U : ℕ → ℕ → ℚ)
    (hU : ∀ n k, ∑ j ∈ Finset.range (n + 1), B n j * U j k = if n = k then 1 else 0) :
    ∀ n k, U n k = T n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    have e1 := hU n k
    have e2 := T_inverse n k
    rw [Finset.sum_range_succ] at e1 e2
    have hs : ∑ j ∈ Finset.range n, B n j * U j k = ∑ j ∈ Finset.range n, B n j * (T j k : ℚ) :=
      Finset.sum_congr rfl (fun j hj => by rw [ih j (Finset.mem_range.1 hj) k])
    have hB : B n n = 1 / (2 * n + 1) := by simp [B]; omega
    have hne : B n n ≠ 0 := by rw [hB]; positivity
    have : B n n * U n k = B n n * (T n k : ℚ) := by linarith
    exact mul_left_cancel₀ hne this

/-- Same for `t` and A101688 (so `t` is A111967). -/
theorem t_unique (U : ℕ → ℕ → ℤ)
    (hU : ∀ n k, ∑ j ∈ Finset.range (n + 1), M n j * U j k = if n = k then 1 else 0) :
    ∀ n k, U n k = t n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    have e1 := hU n k
    have e2 := t_inverse n k
    rw [Finset.sum_range_succ] at e1 e2
    have hs : ∑ j ∈ Finset.range n, M n j * U j k = ∑ j ∈ Finset.range n, M n j * t j k :=
      Finset.sum_congr rfl (fun j hj => by rw [ih j (Finset.mem_range.1 hj) k])
    have hM : M n n = 1 := by
      have h' : n ≤ n ∧ n ≤ 2 * n := by omega
      simp [M, h']
    rw [hM] at e1 e2; linarith

/-- row sums of A111967 -/
def R (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), t n k

lemma sum_t_extend (n m : ℕ) (h : n + 1 ≤ m) :
    ∑ k ∈ Finset.range m, t n k = R n := by
  rw [R]; symm
  apply Finset.sum_subset
  · intro x hx; simp at hx ⊢; omega
  · intro x hx hx'; simp at hx hx'; exact t_lower n x (by omega)

lemma R_zero : R 0 = 1 := by simp [R, t_zero]

lemma R_succ (n : ℕ) : R (n + 1) = if n % 2 = 0 then R (n / 2) else 0 := by
  have : R (n + 1) = ∑ k ∈ Finset.range (n + 2),
      ((if n + 1 = k then (1 : ℤ) else 0) - (if n = k then 1 else 0) +
        (if n % 2 = 0 then t (n / 2) k else 0)) := by
    simp only [R]; exact Finset.sum_congr rfl (fun k _ => t_succ n k)
  rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_range, show n + 1 < n + 2 by omega, show n < n + 2 by omega, ite_true]
  split_ifs with h
  · rw [sum_t_extend _ _ (by omega)]; ring
  · simp

lemma pow_two_succ (n : ℕ) :
    (∃ m, n + 2 = 2 ^ m) ↔ (n % 2 = 0 ∧ ∃ m, n / 2 + 1 = 2 ^ m) := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => simp at hm
    | succ m =>
      rw [pow_succ] at hm
      exact ⟨by omega, m, by omega⟩
  · rintro ⟨h, m, hm⟩
    exact ⟨m + 1, by rw [pow_succ]; omega⟩

open Classical in
/-- Row sums of A111967 are the Fredholm-Rueppel sequence. -/
theorem rowsum_t : ∀ n, R n = A036987 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [R_zero, A036987, ite_pos' (⟨0, rfl⟩ : ∃ m, 0 + 1 = 2 ^ m)]
    | succ n =>
      rw [R_succ, A036987]
      by_cases h : n % 2 = 0
      · rw [ite_pos' h, ih (n / 2) (by omega), A036987]
        have := pow_two_succ n
        by_cases hp : ∃ m, n / 2 + 1 = 2 ^ m
        · rw [ite_pos' hp, ite_pos' (this.2 ⟨h, hp⟩)]
        · rw [ite_neg' hp, ite_neg' (fun h' => hp (this.1 h').2)]
      · rw [ite_neg' h, ite_neg' (fun h' => h ((pow_two_succ n).1 h').1)]

theorem A127750_mod_two (n : ℕ) : A127750 n % 2 = A036987 n := by
  have h : A127750 n = R n + 2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * t n k := by
    simp only [A127750, T, R, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h, rowsum_t, Int.add_mul_emod_self_left, A036987]
  split_ifs <;> rfl

theorem t_values : ∀ n k, t n k = -1 ∨ t n k = 0 ∨ t n k = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    cases n with
    | zero => rw [t_zero]; split_ifs <;> simp
    | succ n =>
      rw [t_succ]
      by_cases h1 : n + 1 = k
      · subst h1
        have : t (n / 2) (n + 1) = 0 := t_lower _ _ (by omega)
        simp [this]
      · by_cases h2 : n = k
        · subst h2
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; simp [t_zero]
          · have : t (n / 2) n = 0 := t_lower _ _ (by omega)
            simp [this]
        · simp only [h1, h2, ite_false, sub_zero, zero_add]
          split_ifs
          · exact ih (n / 2) (by omega) k
          · simp

theorem A127749_rowsum_mod_two (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (T n k % 2) = A111982 n := by
  rw [A111982]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [T]
  rcases t_values n k with h | h | h <;> rw [h]
  · have : (2 * (k : ℤ) + 1) * -1 = -1 + 2 * (-(k : ℤ)) := by ring
    rw [this, Int.add_mul_emod_self_left]; rfl
  · simp
  · have : (2 * (k : ℤ) + 1) * 1 = 1 + 2 * (k : ℤ) := by ring
    rw [this, Int.add_mul_emod_self_left]; rfl
