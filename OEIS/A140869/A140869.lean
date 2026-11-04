/-
OEIS A140869: triangle T(m,n) = floor((2mn + m + n - 2)/2), m ≥ n ≥ 1.
Conjecture (Librandi 2012): if h is not a term then 4h + 5 is prime.
True. Contrapositive proved here: if 4h + 5 = d * e with d, e > 1 then
h = T(m, n) for some m ≥ n ≥ 1.

Checked here (core Lean): `composite_is_term`, for all h, d, e.
Not checked here: nothing (a prime is a number with no factorisation d*e,
d, e > 1).
-/

def T (m n : Nat) : Nat := (2 * m * n + m + n - 2) / 2

theorem odd_of_mul_odd (d e : Nat) (h : (d * e) % 2 = 1) : d % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
  · have : (d * e) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
    omega
  · exact h1

theorem composite_is_term (h d e : Nat) (hde : d * e = 4 * h + 5) (hd : 1 < d) (he : 1 < e) :
    ∃ m n, 1 ≤ n ∧ n ≤ m ∧ T m n = h := by
  have hd2 : d % 2 = 1 := odd_of_mul_odd d e (by omega)
  have he2 : e % 2 = 1 := odd_of_mul_odd e d (by rw [Nat.mul_comm]; omega)
  obtain ⟨a, rfl⟩ : ∃ a, d = 2 * a + 1 := ⟨d / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, e = 2 * b + 1 := ⟨e / 2, by omega⟩
  have key : 4 * (a * b) + 2 * a + 2 * b + 1 = 4 * h + 5 := by
    rw [← hde]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    rw [Nat.mul_comm (2 * a) (2 * b)]
    have : 2 * b * (2 * a) = 4 * (a * b) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm b 2 a, ← Nat.mul_assoc, Nat.mul_comm b a]
    omega
  rcases Nat.le_total b a with hab | hab
  · refine ⟨a, b, by omega, hab, ?_⟩
    unfold T
    have : 2 * a * b = 2 * (a * b) := Nat.mul_assoc 2 a b
    omega
  · refine ⟨b, a, by omega, hab, ?_⟩
    unfold T
    have : 2 * b * a = 2 * (a * b) := by rw [Nat.mul_assoc, Nat.mul_comm b a]
    omega
