/-
NT-F23.2 (Guy, UPINT 3rd ed., F23, Erdős): "n! = 2^a + 2^b only when
n = 1, 2, 3, 4 and 5".

Checked here (core Lean, no Mathlib), for the "+" sign as printed:
* `plus_solutions`: n! = 2^a + 2^b implies n ∈ {2, 3, 4}; and
  `plus_examples`: 2! = 1 + 1, 3! = 4 + 2, 4! = 16 + 8.
  So the printed list is right as an upper bound but n = 1 and n = 5 are not
  solutions (1 < 2 ≤ 2^a + 2^b, and 120 = 1111000₂ has four binary ones).
  Key fact (`sum_mod7`): 2^a + 2^b is never divisible by 7, while 7 ∣ n!
  for n ≥ 7.
Not checked here: the "−" reading n! = 2^a − 2^b (solutions n = 1, ..., 5),
whose proof (2-adic and 3-adic valuations) is in the README.
-/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem seven_dvd (n : Nat) (h : 7 ≤ n) : 7 ∣ fact n := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : 7 ≤ m
    · exact Nat.dvd_trans (ih hm) (Nat.dvd_mul_left _ _)
    · have : m = 6 := by omega
      subst this; decide

theorem pow2_mod7 (a : Nat) : 2 ^ a % 7 = 1 ∨ 2 ^ a % 7 = 2 ∨ 2 ^ a % 7 = 4 := by
  induction a with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem sum_mod7 (a b : Nat) : (2 ^ a + 2 ^ b) % 7 ≠ 0 := by
  rw [Nat.add_mod]
  rcases pow2_mod7 a with h | h | h <;> rcases pow2_mod7 b with h' | h' | h' <;>
    rw [h, h'] <;> decide

theorem small_cases : ∀ a < 10, ∀ b < 10,
    2 ^ a + 2 ^ b ≠ 1 ∧ 2 ^ a + 2 ^ b ≠ 120 ∧ 2 ^ a + 2 ^ b ≠ 720 := by decide

theorem pow_big (a : Nat) (h : 10 ≤ a) : 1024 ≤ 2 ^ a :=
  Nat.le_trans (by decide : 1024 ≤ 2 ^ 10) (Nat.pow_le_pow_right (by decide) h)

theorem plus_solutions (n a b : Nat) (h : fact n = 2 ^ a + 2 ^ b) : n = 2 ∨ n = 3 ∨ n = 4 := by
  by_cases h7 : 7 ≤ n
  · have hd := seven_dvd n h7
    rw [h] at hd
    exact absurd (Nat.mod_eq_zero_of_dvd hd) (sum_mod7 a b)
  · have hf : fact n = 1 ∨ fact n = 2 ∨ fact n = 6 ∨ fact n = 24 ∨ fact n = 120 ∨ fact n = 720 := by
      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hle : fact n ≤ 720 := by omega
    have ha : a < 10 := by
      false_or_by_contra
      have h1 := pow_big a (by omega)
      have h2 := Nat.zero_le (2 ^ b)
      omega
    have hb : b < 10 := by
      false_or_by_contra
      have h1 := pow_big b (by omega)
      have h2 := Nat.zero_le (2 ^ a)
      omega
    have hs := small_cases a ha b hb
    have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | omega
      | (exfalso; simp only [fact] at h; omega)

theorem plus_examples : fact 2 = 2 ^ 0 + 2 ^ 0 ∧ fact 3 = 2 ^ 2 + 2 ^ 1 ∧ fact 4 = 2 ^ 4 + 2 ^ 3 := by
  decide
