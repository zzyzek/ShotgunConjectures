/-
OEIS A029795 (numbers k such that k and k^3 have the same set of decimal
digits).  Conjecture (C. R. Greathouse IV, 2011): there are m, N with
a(n) = m + n for all n ≥ N, i.e. every integer from some point on is a term.
False.

Checked here (core Lean, full statement):
* `no3`: for e ≥ 1 the number 10^e + 1 has no decimal digit 3.
* `cube3`: the digit of (10^e + 1)^3 at position e is 3
  ((10^e+1)^3 = 10^(3e) + 3·10^(2e) + 3·10^e + 1).
* `main`: there is no bound M such that every x ≥ M has the same digit set
  as x^3 (take x = 10^(M+1) + 1).  If a(n) = m + n for n ≥ N, every
  x ≥ a(N) would be a term, so the conjecture fails.
Digit d occurs in x means x / 10^j % 10 = d for some j (leading zeros never
give d = 3, so this matches the decimal digit set for d = 3).
Not checked here: nothing.
-/

def HasDigit (x d : Nat) : Prop := ∃ j, x / 10 ^ j % 10 = d

def SameDigits (x y : Nat) : Prop := ∀ d, d < 10 → (HasDigit x d ↔ HasDigit y d)

theorem pow10_mod (e : Nat) (he : 1 ≤ e) : 10 ^ e % 10 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [Nat.pow_succ]; exact Nat.mul_mod_left _ _

theorem cube3 (e : Nat) (he : 1 ≤ e) : (10 ^ e + 1) ^ 3 / 10 ^ e % 10 = 3 := by
  have hP : 10 ≤ 10 ^ e := by
    have := Nat.pow_le_pow_right (show 10 > 0 by decide) he
    simpa using this
  have h0 := pow10_mod e he
  generalize 10 ^ e = P at hP h0
  have hc : (P + 1) ^ 3 = P * (P * P + 3 * P + 3) + 1 := by grind
  rw [hc, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have h1 : P * P % 10 = 0 := by rw [Nat.mul_mod, h0]
  omega

theorem no3 (e : Nat) (he : 1 ≤ e) (j : Nat) : (10 ^ e + 1) / 10 ^ j % 10 ≠ 3 := by
  by_cases hj0 : j = 0
  · subst hj0
    have := pow10_mod e he
    simp only [Nat.pow_zero, Nat.div_one]
    omega
  by_cases hje : j ≤ e
  · have hpos : 10 ≤ 10 ^ j := by
      have := Nat.pow_le_pow_right (show 10 > 0 by decide) (show 1 ≤ j by omega)
      simpa using this
    have hsplit : 10 ^ e = 10 ^ j * 10 ^ (e - j) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hsplit, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    by_cases hej : e - j = 0
    · rw [hej]; decide
    · have := pow10_mod (e - j) (by omega)
      omega
  · have hlt : 10 ^ e + 1 < 10 ^ j := by
      have h1 : 10 ^ (e + 1) ≤ 10 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 10 ^ (e + 1) = 10 ^ e * 10 := by rw [Nat.pow_succ]
      have h3 : 1 ≤ 10 ^ e := Nat.pow_pos (by decide)
      omega
    rw [Nat.div_eq_of_lt hlt]; decide

theorem main : ¬ ∃ M, ∀ x, M ≤ x → SameDigits x (x ^ 3) := by
  intro ⟨M, hM⟩
  have hbig : M < 10 ^ (M + 1) := by
    have h1 : M + 1 < 10 ^ (M + 1) := Nat.lt_pow_self (n := M + 1) (by decide)
    omega
  have h := hM (10 ^ (M + 1) + 1) (by omega) 3 (by decide)
  have hc : HasDigit ((10 ^ (M + 1) + 1) ^ 3) 3 := ⟨M + 1, cube3 (M + 1) (by omega)⟩
  obtain ⟨j, hj⟩ := h.mpr hc
  exact no3 (M + 1) (by omega) j hj
