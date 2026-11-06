import Mathlib

/-
OEIS A054096 (offset 2): T(n,2) for the array T of A054090.
A054090: T(n,0) = 1 for n >= 0, T(n,1) = r(n-1), T(n,k) = T(n,k-1) - (-1)^k r(n-k)
for k = 2, ..., n, n >= 2, where r(h) is the sum of row h of T.
A006183 (offset 1, data 1, 2, 6, 22, 98, ...): "a(n) = (n+1)*a(n-1) + (2-n)*a(n-2)"
with a[0] = 1, a[1] = 2 in the entry's Mathematica program; in the OEIS offset 1
this is a(1) = 1, a(2) = 2, a(n) = n a(n-1) + (3-n) a(n-2) (the entry's Magma line).
Conjecture (R. Stephan, Jan 15 2004): A054096 is A006183 shifted right, i.e.
A054096(n) = A006183(n-1) for n >= 2.

Definitions.  `T n k` follows the A054090 rule literally (well-founded recursion;
T n k = 0 for k > n, never used), `r n` = sum of row n, `A054096 n = T n 2`,
`A006183` by the recurrence above with the data's initial terms.

Main theorem.
* `A054096_eq_A006183_shift`: for every n >= 2, A054096 n = A006183 (n - 1).

Route.  `pair`: T(m+1,k) + T(m,k-1) = r(m) for 2 <= k <= m+1.  Summing over a row,
`r_succ`: r(m+1) = m r(m) + 2 (the recurrence stated, unproved, in A054091).
`T_two`: T(m+2,2) = r(m+1) - r(m); the three-term recurrence follows.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py recomputes both sequences).
-/

namespace OEIS

def T : ℕ → ℕ → ℤ
  | _, 0 => 1
  | n, k + 1 =>
    if h : k + 1 ≤ n then
      if k = 0 then ∑ j ∈ Finset.range n, T (n - 1) j
      else T n k - (-1) ^ (k + 1) * ∑ j ∈ Finset.range (n - k), T (n - k - 1) j
    else 0
termination_by n k => (n, k)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

/-- Row sums r(h) (A054091). -/
def r (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), T n j

def A054096 (n : ℕ) : ℤ := T n 2

/-- A006183 with the OEIS offset 1 (index 0 unused). -/
def A006183 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | (n + 3) => (n + 3) * A006183 (n + 2) + (3 - (n + 3 : ℤ)) * A006183 (n + 1)

theorem T_zero (n : ℕ) : T n 0 = 1 := by
  rw [T]

theorem T_one (m : ℕ) : T (m + 1) 1 = r m := by
  rw [T]
  split_ifs <;> first | omega | simp [r]

theorem T_succ (n k : ℕ) (hk : 1 ≤ k) (h : k + 1 ≤ n) :
    T n (k + 1) = T n k - (-1) ^ (k + 1) * r (n - k - 1) := by
  rw [T]
  split_ifs <;> first | omega | rw [r, show n - k - 1 + 1 = n - k by omega]

theorem pair (m : ℕ) : ∀ k, 2 ≤ k → k ≤ m + 1 → T (m + 1) k + T m (k - 1) = r m := by
  intro k hk1 hk2
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [T_succ (m' + 1 + 1) 1 le_rfl (by omega), T_one, show 1 + 1 - 1 = 1 from rfl, T_one,
        show m' + 1 + 1 - 1 - 1 = m' by omega]
      ring
    · have ih' := ih hk (by omega)
      rw [T_succ (m + 1) k (by omega) (by omega), show k + 1 - 1 = (k - 1) + 1 by omega,
        T_succ m (k - 1) (by omega) (by omega), show k - 1 + 1 = k by omega,
        show m + 1 - k - 1 = m - (k - 1) - 1 by omega, pow_succ]
      linear_combination ih'

theorem r_zero : r 0 = 1 := by simp [r, T_zero]

theorem r_succ (m : ℕ) : r (m + 1) = m * r m + 2 := by
  have hsum : ∑ i ∈ Finset.range m, T (m + 1) (i + 2)
      = ∑ i ∈ Finset.range m, (r m - T m (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have := pair m (i + 2) (by omega) (by simp at hi; omega)
    rw [show i + 2 - 1 = i + 1 by omega] at this
    linear_combination this
  have hr : r m = ∑ i ∈ Finset.range m, T m (i + 1) + 1 := by
    rw [r, Finset.sum_range_succ', T_zero]
  have hr1 : r (m + 1) = ∑ i ∈ Finset.range m, T (m + 1) (i + 2) + T (m + 1) 1 + 1 := by
    rw [r, Finset.sum_range_succ', Finset.sum_range_succ', T_zero]
  rw [hr1, hsum, T_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  linear_combination (1 - (m : ℤ) + m) * hr - hr + hr

theorem T_two (m : ℕ) : T (m + 2) 2 = r (m + 1) - r m := by
  rw [T_succ (m + 2) 1 le_rfl (by omega), T_one, show m + 2 - 1 - 1 = m by omega]
  ring

theorem T_two_eq (m : ℕ) : T (m + 2) 2 = A006183 (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ =>
      rw [T_two, r_succ, r_zero]; simp [A006183]
    | 1, _ =>
      rw [T_two, r_succ, r_succ, r_zero]; simp [A006183]
    | (m + 2), ih =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      rw [T_two] at h1 h0 ⊢
      show r (m + 2 + 1) - r (m + 2) = (m + 3) * A006183 (m + 2) + (3 - (m + 3 : ℤ)) * A006183 (m + 1)
      rw [← h1, ← h0]
      have e3 := r_succ (m + 2)
      have e2 := r_succ (m + 1)
      have e1 := r_succ m
      push_cast at e3 e2 e1 ⊢
      linear_combination e3 - 2 * e2 + e1

/-- Stephan's conjecture: A054096(n) = A006183(n-1) for every n >= 2. -/
theorem A054096_eq_A006183_shift (n : ℕ) (hn : 2 ≤ n) : A054096 n = A006183 (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [A054096, T_two_eq, show m + 2 - 1 = m + 1 by omega]
