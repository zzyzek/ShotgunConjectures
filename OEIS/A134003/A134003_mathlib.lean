/-
OEIS A134003 (n with n^2 + (n+5)^2 prime), conjecture (Layman 2007): if n is
in the sequence then n(n+5) = a(a+5) + b(b+5) is not solvable.

Main theorem `A134003_positive`: for natural n with n^2 + (n+5)^2 prime there
are no positive integers a, b with n(n+5) = a(a+5) + b(b+5).  This is the
README result for the intended reading (positive a, b).  The literal reading
("in integers") is false, `A134003_literal_false`: a = n, b = 0 always works.

Proof: M = n^2 + (n+5)^2 = (a+b+5)^2 + (a-b)^2 whenever the equation holds,
and a prime has only one representation as a sum of two squares of
nonnegative integers up to order (`sq_add_sq_unique`, proved here from
p ∣ (ad-bc)(ad+bc) and (ad±bc)^2 + (ac∓bd)^2 = p^2).

Not checked: nothing outside Lean.
-/
import Mathlib

/-- If x is a multiple of p and x^2 ≤ p^2 then x ∈ {-p, 0, p}. -/
lemma mult_small {p x : ℤ} (hp : 0 < p) (hd : p ∣ x) (hs : x ^ 2 ≤ p ^ 2) :
    x = -p ∨ x = 0 ∨ x = p := by
  obtain ⟨t, rfl⟩ := hd
  have ht : t ^ 2 ≤ 1 := by
    have : p ^ 2 * t ^ 2 ≤ p ^ 2 * 1 := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have h1 : -1 ≤ t := by nlinarith
  have h2 : t ≤ 1 := by nlinarith
  interval_cases t <;> simp

lemma sq_sum_zero {a b c d : ℤ} (h : (a - c) ^ 2 + (b - d) ^ 2 = 0) : a = c ∧ b = d := by
  have h3 : (a - c) ^ 2 = 0 := by linarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  have h4 : (b - d) ^ 2 = 0 := by linarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3),
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)⟩

/-- Uniqueness of the two-squares representation of a prime. -/
lemma sq_add_sq_unique {p : ℕ} (hp : p.Prime) {a b c d : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : (p : ℤ) = a ^ 2 + b ^ 2) (h2 : (p : ℤ) = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- No square is a prime, so all four entries are positive.
  have nsq : ∀ x : ℤ, 0 ≤ x → (p : ℤ) ≠ x ^ 2 := by
    intro x hx hpx
    have : (p : ℤ) = (x.toNat : ℤ) ^ 2 := by rw [Int.toNat_of_nonneg hx]; exact hpx
    have : p = x.toNat ^ 2 := by exact_mod_cast this
    exact Nat.Prime.not_prime_pow le_rfl (this ▸ hp)
  have ha' : 0 < a := lt_of_le_of_ne ha (by rintro rfl; exact nsq b hb (by rw [h1]; ring))
  have hb' : 0 < b := lt_of_le_of_ne hb (by rintro rfl; exact nsq a ha (by rw [h1]; ring))
  have hc' : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact nsq d hd (by rw [h2]; ring))
  have hd' : 0 < d := lt_of_le_of_ne hd (by rintro rfl; exact nsq c hc (by rw [h2]; ring))
  have key : (a * d - b * c) * (a * d + b * c) = (p : ℤ) * (a ^ 2 - c ^ 2) := by
    rw [h1] at *; nlinarith [h1, h2]
  have e1 : (a * d + b * c) ^ 2 + (a * c - b * d) ^ 2 = (p : ℤ) ^ 2 := by
    rw [sq (p : ℤ)]; nth_rewrite 1 [h1]; rw [h2]; ring
  have e2 : (a * d - b * c) ^ 2 + (a * c + b * d) ^ 2 = (p : ℤ) ^ 2 := by
    rw [sq (p : ℤ)]; nth_rewrite 1 [h1]; rw [h2]; ring
  have hdvd : (p : ℤ) ∣ (a * d - b * c) * (a * d + b * c) := ⟨_, key⟩
  rcases hpz.dvd_or_dvd hdvd with hdv | hdv
  · rcases mult_small hp0 hdv (by nlinarith) with h | h | h
    · have : (a * c + b * d) ^ 2 = 0 := by rw [h] at e2; linarith
      have : a * c + b * d = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      nlinarith [mul_pos ha' hc', mul_pos hb' hd']
    · have hs : (a * c + b * d) ^ 2 = (p : ℤ) ^ 2 := by rw [h] at e2; linarith
      have hs' : a * c + b * d = p := by
        have := (sq_eq_sq₀ (by positivity) hp0.le).mp hs; exact this
      left
      have : (a - c) ^ 2 + (b - d) ^ 2 = 0 := by linear_combination (-1) * h1 - h2 - 2 * hs'
      exact sq_sum_zero this
    · have : (a * c + b * d) ^ 2 = 0 := by rw [h] at e2; linarith
      have : a * c + b * d = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      nlinarith [mul_pos ha' hc', mul_pos hb' hd']
  · rcases mult_small hp0 hdv (by nlinarith) with h | h | h
    · nlinarith [mul_pos ha' hd', mul_pos hb' hc']
    · nlinarith [mul_pos ha' hd', mul_pos hb' hc']
    · right
      have : (a - d) ^ 2 + (b - c) ^ 2 = 0 := by linear_combination (-1) * h1 - h2 - 2 * h
      exact sq_sum_zero this

theorem A134003_positive (n a b : ℕ) (hM : (n ^ 2 + (n + 5) ^ 2).Prime)
    (ha : 0 < a) (hb : 0 < b) : n * (n + 5) ≠ a * (a + 5) + b * (b + 5) := by
  intro heq
  -- Symmetric in a, b; reduce to b ≤ a.
  wlog hab : b ≤ a generalizing a b
  · exact this b a hb ha (by rw [heq]; ring) (by omega)
  have hz : ((n ^ 2 + (n + 5) ^ 2 : ℕ) : ℤ) = ((a : ℤ) + b + 5) ^ 2 + ((a : ℤ) - b) ^ 2 := by
    have : ((n * (n + 5) : ℕ) : ℤ) = ((a * (a + 5) + b * (b + 5) : ℕ) : ℤ) := by rw [heq]
    push_cast at this ⊢; nlinarith [this]
  have hz2 : ((n ^ 2 + (n + 5) ^ 2 : ℕ) : ℤ) = ((n : ℤ) + 5) ^ 2 + (n : ℤ) ^ 2 := by
    push_cast; ring
  rcases sq_add_sq_unique hM (by positivity) (by omega) (by positivity) (by positivity) hz hz2
    with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem A134003_literal_false (n : ℤ) :
    ∃ a b : ℤ, n * (n + 5) = a * (a + 5) + b * (b + 5) := ⟨n, 0, by ring⟩
