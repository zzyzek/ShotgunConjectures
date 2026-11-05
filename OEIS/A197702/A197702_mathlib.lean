/-
OEIS A197702: a(n) is the smallest positive k with n = ±1 ±3 ± ... ±(2k-1)
(offset 1).  Conjecture (J. W. Layman, entry text): a(k^2) = k; for
(k-1)^2 < n < k^2, a(n) = k+2 if k^2 - n = 4, k+1 if k^2 - n is odd, and k
otherwise.

Definitions.  `S k` is the finite set of all values ±1 ±3 ... ±(2k-1)
(`S 0 = {0}`, `S (k+1)` = (S k + (2k+1)) ∪ (S k - (2k+1))).  `a n` is the
infimum of {k | 0 < k ∧ n ∈ S k}.  `rule n` is the conjectured value with
k = ⌊√(n-1)⌋ + 1, the k with (k-1)^2 < n ≤ k^2.

Main theorems.
* `mem_S`: m ∈ S k ↔ -k^2 ≤ m ≤ k^2, k^2 - m even, m ≠ k^2 - 4, m ≠ 4 - k^2
  (for all k; for k ≥ 2 this says the subset sums of {1, 3, ..., 2k-1} are
  [0, k^2] minus {2, k^2 - 2}).
* `A197702_square`: a(k^2) = k for k ≥ 1.
* `A197702_between`: for (k-1)^2 < n < k^2, a(n) is the conjectured value.
* `A197702_conjecture`: for every n ≥ 1, a(n) = rule n.

Proof.  `mem_S` by induction on k: the step is linear arithmetic in
K = k^2 and k once K is known for k ≤ 3 and K ≥ 4k for k ≥ 4.  For n with
(k-1)^2 < n ≤ k^2 no j ≤ k-1 works (n > j^2), and the conditions of
`mem_S` for j = k, k+1, k+2 give the three cases.

Not checked: nothing outside Lean (certificate/check.py compares `rule`
with the b-file for n ≤ 10000 and with brute force for n ≤ 20000).
-/
import Mathlib

/-- All values ±1 ±3 ... ±(2k-1). -/
def S : ℕ → Finset ℤ
  | 0 => {0}
  | k + 1 => (S k).image (· + (2 * k + 1)) ∪ (S k).image (· - (2 * k + 1))

/-- A197702(n): least positive k with n ∈ S k. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ (n : ℤ) ∈ S k}

/-- The conjectured value. -/
def rule (n : ℕ) : ℕ :=
  let k := Nat.sqrt (n - 1) + 1
  if k ^ 2 = n then k
  else if k ^ 2 - n = 4 then k + 2
  else if (k ^ 2 - n) % 2 = 1 then k + 1
  else k

theorem rule_data :
    (List.range' 1 40).map rule =
      [1, 2, 3, 2, 5, 4, 3, 4, 3, 4, 5, 6, 5, 4, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 6, 7, 6,
       7, 6, 7, 8, 7, 6, 7, 6, 7, 8, 7, 8] := by
  decide +kernel

lemma mem_S_succ (k : ℕ) (m : ℤ) :
    m ∈ S (k + 1) ↔ (m - (2 * k + 1) ∈ S k ∨ m + (2 * k + 1) ∈ S k) := by
  simp only [S, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · left; simpa using hx
    · right; simpa using hx
  · rintro (h | h)
    · left; exact ⟨_, h, by ring⟩
    · right; exact ⟨_, h, by ring⟩

theorem mem_S (k : ℕ) (m : ℤ) :
    m ∈ S k ↔ (-((k : ℤ) ^ 2) ≤ m ∧ m ≤ (k : ℤ) ^ 2 ∧ ((k : ℤ) ^ 2 - m) % 2 = 0 ∧
      m ≠ (k : ℤ) ^ 2 - 4 ∧ m ≠ 4 - (k : ℤ) ^ 2) := by
  induction k generalizing m with
  | zero =>
    simp only [S, Finset.mem_singleton, Nat.cast_zero]
    norm_num
    omega
  | succ k ih =>
    rw [mem_S_succ, ih, ih]
    have hK : ((k + 1 : ℕ) : ℤ) ^ 2 = (k : ℤ) ^ 2 + 2 * k + 1 := by push_cast; ring
    rw [hK]
    have hs : ((k : ℤ) = 0 ∧ (k : ℤ) ^ 2 = 0) ∨ ((k : ℤ) = 1 ∧ (k : ℤ) ^ 2 = 1) ∨
        ((k : ℤ) = 2 ∧ (k : ℤ) ^ 2 = 4) ∨ ((k : ℤ) = 3 ∧ (k : ℤ) ^ 2 = 9) ∨
        (4 ≤ (k : ℤ) ∧ 4 * (k : ℤ) ≤ (k : ℤ) ^ 2) := by
      rcases (by omega : k ≤ 3 ∨ 4 ≤ k) with hk | hk
      · interval_cases k <;> norm_num
      · right; right; right; right
        have : (4 : ℤ) ≤ k := by exact_mod_cast hk
        exact ⟨this, by nlinarith⟩
    generalize (k : ℤ) ^ 2 = K at *
    generalize (k : ℤ) = x at *
    omega

/-- Membership of a positive integer, in natural-number form. -/
lemma reach (j n : ℕ) :
    (n : ℤ) ∈ S j ↔ (n ≤ j ^ 2 ∧ (j ^ 2 - n) % 2 = 0 ∧ n + 4 ≠ j ^ 2 ∧ n + j ^ 2 ≠ 4) := by
  rw [mem_S]
  have : ((j ^ 2 : ℕ) : ℤ) = (j : ℤ) ^ 2 := by push_cast; ring
  rw [← this]
  generalize j ^ 2 = J
  omega

lemma not_reach_small (j n k : ℕ) (h1 : (k - 1) ^ 2 < n) (hj : j ≤ k - 1) :
    (n : ℤ) ∉ S j := by
  rw [reach]
  have : j ^ 2 ≤ (k - 1) ^ 2 := Nat.pow_le_pow_left hj 2
  omega

lemma a_eq (n v : ℕ) (hv0 : 0 < v) (hv : (n : ℤ) ∈ S v)
    (hmin : ∀ j, 0 < j → j < v → (n : ℤ) ∉ S j) : a n = v := by
  apply IsLeast.csInf_eq
  refine ⟨⟨hv0, hv⟩, fun j hj => ?_⟩
  by_contra h
  exact hmin j hj.1 (by omega) hj.2

/-- Squares of positive integers are 1, 4 or at least 9. -/
lemma sq_cases (k : ℕ) (hk : 1 ≤ k) :
    (k = 1 ∧ k ^ 2 = 1) ∨ (k = 2 ∧ k ^ 2 = 4) ∨ (3 ≤ k ∧ 9 ≤ k ^ 2) := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · norm_num
  · norm_num
  · right; right; exact ⟨hk3, by nlinarith⟩

theorem A197702_square (k : ℕ) (hk : 1 ≤ k) : a (k ^ 2) = k := by
  have hlt : (k - 1) ^ 2 < k ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hs := sq_cases k hk
  apply a_eq _ _ (by omega)
  · rw [reach]
    generalize k ^ 2 = K at *
    omega
  · intro j _ hj
    exact not_reach_small j _ k hlt (by omega)

theorem A197702_between (k n : ℕ) (h1 : (k - 1) ^ 2 < n) (h2 : n < k ^ 2) :
    a n = if k ^ 2 - n = 4 then k + 2 else if (k ^ 2 - n) % 2 = 1 then k + 1 else k := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at h2
    · exact h
  have hs := sq_cases k hk
  have e1 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  have e2 : (k + 2) ^ 2 = k ^ 2 + 4 * k + 4 := by ring
  have hsmall : ∀ j, j < k → (n : ℤ) ∉ S j := fun j hj => not_reach_small j n k h1 (by omega)
  split_ifs with hd ho
  · apply a_eq _ _ (by omega)
    · rw [reach, e2]
      generalize k ^ 2 = K at *
      omega
    · intro j _ hj
      rcases (by omega : j < k ∨ j = k ∨ j = k + 1) with hj | rfl | rfl
      · exact hsmall j hj
      · rw [reach]
        generalize j ^ 2 = K at *
        omega
      · rw [reach, e1]
        generalize k ^ 2 = K at *
        omega
  · apply a_eq _ _ (by omega)
    · rw [reach, e1]
      generalize k ^ 2 = K at *
      omega
    · intro j _ hj
      rcases (by omega : j < k ∨ j = k) with hj | rfl
      · exact hsmall j hj
      · rw [reach]
        generalize j ^ 2 = K at *
        omega
  · apply a_eq _ _ (by omega)
    · rw [reach]
      generalize k ^ 2 = K at *
      omega
    · intro j _ hj
      exact hsmall j hj

theorem A197702_conjecture (n : ℕ) (hn : 1 ≤ n) : a n = rule n := by
  have h1 : (Nat.sqrt (n - 1) + 1 - 1) ^ 2 < n := by
    have := Nat.sqrt_le' (n - 1)
    simp only [Nat.add_sub_cancel]
    omega
  have h2 : n ≤ (Nat.sqrt (n - 1) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' (n - 1)
    rw [Nat.succ_eq_add_one] at this
    omega
  simp only [rule]
  by_cases hsq : (Nat.sqrt (n - 1) + 1) ^ 2 = n
  · simp only [hsq, ↓reduceIte]
    conv_lhs => rw [← hsq]
    exact A197702_square _ (by omega)
  · simp only [hsq, ↓reduceIte]
    exact A197702_between _ n h1 (by omega)
