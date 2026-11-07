/-
OEIS A094044: a(1) = 2; alternately a prime (odd n) and a nonprime (even n), not used
earlier, such that the decimal concatenation of each pair of consecutive terms is prime.
Old comment "Conjecture: 5 is the only nonmember" (Wilson 2004), replaced in 2017 after
R. Israel noted that every term after a(1) is odd and does not end in 5.

`A094044_cat x y` is the decimal concatenation x * 10^(number of digits of y) + y.
  * `A094044_odd_not5`: for any sequence of positive integers with a(1) = 2 whose consecutive
    concatenations are all prime, every a(n) with n >= 2 is odd and not divisible by 5.
  * `A094044_main`: such a sequence never takes the value 4 (nor 6, 15, ...), so 5 is not
    the only nonmember.
Checked: the above, for every sequence with these properties (the greedy choice is not used).
Not checked: that A094044 has these properties; that is its definition (all terms positive,
a(1) = 2, consecutive concatenations prime).
-/
import Mathlib

/-- Decimal concatenation of x and y. -/
def A094044_cat (x y : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 y).length + y

theorem A094044_cat_mod (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    10 ≤ A094044_cat x y ∧ A094044_cat x y % 10 = y % 10 := by
  unfold A094044_cat
  have hL : 1 ≤ (Nat.digits 10 y).length := by
    rcases h : Nat.digits 10 y with _ | ⟨d, l⟩
    · rw [Nat.digits_eq_nil_iff_eq_zero] at h
      omega
    · simp
  obtain ⟨m, hm⟩ : ∃ m, (Nat.digits 10 y).length = m + 1 := ⟨_, (Nat.sub_add_cancel hL).symm⟩
  rw [hm, pow_succ]
  have : 1 ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
  constructor
  · nlinarith
  · rw [Nat.add_mod, show x * (10 ^ m * 10) = 10 * (x * 10 ^ m) by ring, Nat.mul_mod_right]
    simp

theorem A094044_odd_not5 (a : ℕ → ℕ) (hpos : ∀ n, 1 ≤ n → 1 ≤ a n)
    (hcat : ∀ n, 1 ≤ n → (A094044_cat (a n) (a (n + 1))).Prime) (n : ℕ) (hn : 2 ≤ n) :
    a n % 2 = 1 ∧ a n % 5 ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hp := hcat m (by omega)
  obtain ⟨h10, hmod⟩ := A094044_cat_mod (a m) (a (m + 1)) (hpos m (by omega)) (hpos _ (by omega))
  constructor
  · by_contra h
    have h2 : 2 ∣ A094044_cat (a m) (a (m + 1)) := by omega
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h' | h' <;> omega
  · intro h
    have h5 : 5 ∣ A094044_cat (a m) (a (m + 1)) := by omega
    rcases hp.eq_one_or_self_of_dvd 5 h5 with h' | h' <;> omega

theorem A094044_main (a : ℕ → ℕ) (h1 : a 1 = 2) (hpos : ∀ n, 1 ≤ n → 1 ≤ a n)
    (hcat : ∀ n, 1 ≤ n → (A094044_cat (a n) (a (n + 1))).Prime) :
    ∀ n, 1 ≤ n → a n ≠ 4 := by
  intro n hn h4
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    omega
  · have := (A094044_odd_not5 a hpos hcat n h).1
    omega
