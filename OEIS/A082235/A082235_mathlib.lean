/-
OEIS A081847 / A082235: the conjecture "every triangular number other than 3, 6 and 10 is a
member of A082235" is false.

A081847: a(1) = 1, a(n) = smallest positive number such that the concatenation of a(n-1) and
a(n) is a triangular number not obtained earlier. A082235(n) = concat(A081847(n), A081847(n+1)).

Checked here: for EVERY sequence a with a 1 = 1 and, for n >= 1, a (n+1) > 0 and
concat (a n) (a (n+1)) triangular (a property the OEIS sequence has by definition; minimality
and "not obtained earlier" are not used), the concatenations concat (a n) (a (n+1)), n >= 1,
never equal 1, 21, 28, 45, 78 or 91, all of which are triangular and differ from 3, 6, 10.
Not checked: that the greedy sequence exists (it is not needed).
-/
import Mathlib

/-- Decimal concatenation of x and y (y > 0 has no leading zeros). -/
def concat (x y : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 y).length + y

def IsTri (t : ℕ) : Prop := ∃ m, t = m * (m + 1) / 2

/-- Last digit of a triangular number. -/
theorem tri_mod10 (m : ℕ) :
    (m * (m + 1) / 2) % 10 ∈ ({0, 1, 3, 5, 6, 8} : Finset ℕ) := by
  have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  obtain ⟨t, ht⟩ := h2
  have ht' : m * (m + 1) / 2 = t := by omega
  have hm : m * (m + 1) % 20 = (m % 20) * (m % 20 + 1) % 20 := by
    simp [Nat.mul_mod, Nat.add_mod]
  have hr : m % 20 < 20 := Nat.mod_lt _ (by norm_num)
  rw [ht']
  have key : (2 * t) % 20 ∈ ({0, 2, 6, 10, 12, 16} : Finset ℕ) := by
    rw [← ht, hm]
    interval_cases (m % 20) <;> simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at key ⊢
  omega

theorem concat_mod10 (x y : ℕ) (hy : 0 < y) : concat x y % 10 = y % 10 := by
  unfold concat
  have hL : (Nat.digits 10 y).length ≠ 0 := by
    simp [Nat.digits_ne_nil_iff_ne_zero, hy.ne']
  obtain ⟨L, hL'⟩ := Nat.exists_eq_succ_of_ne_zero hL
  rw [hL', pow_succ, show x * (10 ^ L * 10) = 10 * (x * 10 ^ L) by ring, Nat.mul_add_mod]

theorem concat_two_digit (x y v : ℕ) (hx : 0 < x) (hy : 0 < y) (hv : v < 100)
    (h : concat x y = v) : x = v / 10 ∧ y = v % 10 := by
  unfold concat at h
  have hlt : y < 10 ^ (Nat.digits 10 y).length := Nat.lt_base_pow_length_digits (by norm_num)
  have hL : (Nat.digits 10 y).length ≠ 0 := by
    simp [Nat.digits_ne_nil_iff_ne_zero, hy.ne']
  rcases Nat.lt_or_ge (Nat.digits 10 y).length 2 with h1 | h1
  · have : (Nat.digits 10 y).length = 1 := by omega
    rw [this] at h hlt
    omega
  · have : 100 ≤ 10 ^ (Nat.digits 10 y).length :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)
    have : 100 ≤ x * 10 ^ (Nat.digits 10 y).length := le_trans this (Nat.le_mul_of_pos_left _ hx)
    omega

/-- Main theorem: for any sequence with the defining property of A081847, the members
concat (a n) (a (n+1)) of A082235 avoid 1, 21, 28, 45, 78, 91. -/
theorem A082235_conjecture_false (a : ℕ → ℕ) (h1 : a 1 = 1)
    (hpos : ∀ n, 1 ≤ n → 0 < a (n + 1))
    (htri : ∀ n, 1 ≤ n → IsTri (concat (a n) (a (n + 1)))) :
    ∀ n, 1 ≤ n → concat (a n) (a (n + 1)) ∉ ({1, 21, 28, 45, 78, 91} : Finset ℕ) := by
  -- every term ends in 0, 1, 3, 5, 6 or 8
  have hlast : ∀ n, 1 ≤ n → a n % 10 ∈ ({0, 1, 3, 5, 6, 8} : Finset ℕ) := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this; simp [h1]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, hm⟩ := htri k (by omega)
      rw [← concat_mod10 (a k) (a (k + 1)) (hpos k (by omega)), hm]
      exact tri_mod10 m
  have hposn : ∀ n, 1 ≤ n → 0 < a n := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this; simp [h1]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact hpos k (by omega)
  intro n hn hmem
  have hx := hposn n hn
  have hy := hpos n hn
  have hl := hlast n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hl
  rcases hmem with h | h | h | h | h | h <;>
  · obtain ⟨hxv, -⟩ := concat_two_digit _ _ _ hx hy (by omega) h
    omega

/-- The excluded values are triangular. -/
theorem excluded_are_triangular :
    IsTri 1 ∧ IsTri 21 ∧ IsTri 28 ∧ IsTri 45 ∧ IsTri 78 ∧ IsTri 91 :=
  ⟨⟨1, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩, ⟨9, rfl⟩, ⟨12, rfl⟩, ⟨13, rfl⟩⟩
