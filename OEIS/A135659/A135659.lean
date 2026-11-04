/-
OEIS A135659 (a(n) = 24n + 7). Conjecture: every Mersenne prime > 3 is a
term. True: if 2^n - 1 > 3 is not divisible by 3 then n is odd and ≥ 3, and
then 2^n - 1 ≡ 7 (mod 24). Every Mersenne prime > 3 satisfies the hypotheses.

Checked here (core Lean): `mersenne_mod_24`, for every n.
Not checked here: nothing beyond "a prime > 3 is not divisible by 3".
-/

theorem pow_odd_mod (j : Nat) : 2 ^ (2 * j + 3) % 24 = 8 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e : 2 ^ (2 * (j + 1) + 3) = 4 * 2 ^ (2 * j + 3) := by
      rw [show 2 * (j + 1) + 3 = (2 * j + 3) + 2 by omega, Nat.pow_add]; omega
    rw [e, Nat.mul_mod, ih]

theorem pow_even_mod3 (j : Nat) : 2 ^ (2 * j) % 3 = 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e : 2 ^ (2 * (j + 1)) = 4 * 2 ^ (2 * j) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.pow_add]; omega
    rw [e, Nat.mul_mod, ih]

theorem mersenne_mod_24 (n : Nat) (hbig : 2 ^ n - 1 > 3) (h3 : (2 ^ n - 1) % 3 ≠ 0) :
    (2 ^ n - 1) % 24 = 7 := by
  have hn : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  generalize n / 2 = j at hn
  rcases hn with hj | hj
  · subst hj
    have := pow_even_mod3 j
    omega
  · subst hj
    have hj1 : j ≥ 1 := by
      rcases j with _ | j
      · simp at hbig
      · omega
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := pow_odd_mod i
    rw [show 2 * (i + 1) + 1 = 2 * i + 3 by omega] at hbig h3 ⊢
    omega
