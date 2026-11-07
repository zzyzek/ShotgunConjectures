import Mathlib

/-!
# OEIS A228916: indices of primes in A108300 are 1 and multiples of 3

A108300: `a 0 = 1`, `a 1 = 5`, `a (n+2) = 3 a (n+1) + a n`.
A228916 lists the `n` with `a n` prime; the comment conjectures `3 ∣ n` for every term but the first.

Checked: `A228916_main : Nat.Prime (a n) → n = 1 ∨ 3 ∣ n`. Reason: `a n mod 10` has period 12;
`n ≡ 2 (mod 3)` gives `a n` even and `> 2`, `n ≡ 1 (mod 3)` gives `5 ∣ a n` and `a n > 5` for `n > 1`.
Not checked: nothing beyond reading the definition.
-/

namespace A228916

def a : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 3 * a (n + 1) + a n

def t (r : ℕ) : ℕ := [1, 5, 6, 3, 5, 8, 9, 5, 4, 7, 5, 2].getD r 0

theorem mod10 : ∀ n, a n % 10 = t (n % 12) ∧ a (n + 1) % 10 = t ((n + 1) % 12) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    show (3 * a (n + 1) + a n) % 10 = t ((n + 2) % 12)
    rw [Nat.add_mod, Nat.mul_mod, ih0, ih1]
    rcases (by omega : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 = 6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11) with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
    · have h1 : (n + 1) % 12 = 1 := by omega
      have h2 : (n + 2) % 12 = 2 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 2 := by omega
      have h2 : (n + 2) % 12 = 3 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 3 := by omega
      have h2 : (n + 2) % 12 = 4 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 4 := by omega
      have h2 : (n + 2) % 12 = 5 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 5 := by omega
      have h2 : (n + 2) % 12 = 6 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 6 := by omega
      have h2 : (n + 2) % 12 = 7 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 7 := by omega
      have h2 : (n + 2) % 12 = 8 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 8 := by omega
      have h2 : (n + 2) % 12 = 9 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 9 := by omega
      have h2 : (n + 2) % 12 = 10 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 10 := by omega
      have h2 : (n + 2) % 12 = 11 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 11 := by omega
      have h2 : (n + 2) % 12 = 0 := by omega
      rw [hr, h1, h2]; decide
    · have h1 : (n + 1) % 12 = 0 := by omega
      have h2 : (n + 2) % 12 = 1 := by omega
      rw [hr, h1, h2]; decide

theorem mono : ∀ n, a n < a (n + 1) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih => show a (n + 1) < 3 * a (n + 1) + a n; omega

theorem ge (n : ℕ) (h : 2 ≤ n) : 16 ≤ a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h' | h'
    · interval_cases n
      · omega
      · decide
    · have := mono n; have := ih h'; omega

theorem A228916_main (n : ℕ) (hp : Nat.Prime (a n)) : n = 1 ∨ 3 ∣ n := by
  have hm := (mod10 n).1
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · right; omega
  · by_cases h1 : n = 1
    · left; exact h1
    · exfalso
      have h5 : 5 ∣ a n := by
        rcases (by omega : n % 12 = 1 ∨ n % 12 = 4 ∨ n % 12 = 7 ∨ n % 12 = 10) with r | r | r | r <;>
          rw [r] at hm <;> norm_num [t] at hm <;> omega
      have := ge n (by omega)
      rcases (Nat.dvd_prime hp).mp h5 with h' | h' <;> omega
  · exfalso
    have h2 : 2 ∣ a n := by
      rcases (by omega : n % 12 = 2 ∨ n % 12 = 5 ∨ n % 12 = 8 ∨ n % 12 = 11) with r | r | r | r <;>
        rw [r] at hm <;> norm_num [t] at hm <;> omega
    have := ge n (by omega)
    rcases (Nat.dvd_prime hp).mp h2 with h' | h' <;> omega
