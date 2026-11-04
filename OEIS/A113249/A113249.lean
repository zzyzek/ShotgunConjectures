/-
OEIS A113249: the m = 3 member of C. Dement's family
a(m,n) = m^4 a(n-4) + (2m)^2 a(n-3) - 4 a(n-1), a(0) = -1, a(1) = 4,
a(2) = -13 + 6(m-1) + 3(m-1)^2, a(3) = (m^2-8)^2.
Conjecture (in A113249 and A113249): a(m, 2n+1) is a perfect square for all m, n.
True for every integer m: a(m, 2n+1) = y(m, n)^2 with
y(n) = 4 y(n-1) - m^2 y(n-2), y(0) = 2, y(1) = 8 - m^2.

Checked here (core Lean, full statement, uniform in m : Int):
* `odd_rec`: n ↦ a(m, 2n+1) satisfies the order-4 recurrence with
  characteristic polynomial (X - m^2)^2 (X^2 + (2m^2 - 16) X + m^4).
* `sq_rec3`, `sq_rec4`: n ↦ y(m, n)^2 satisfies (X - m^2)(X^2 + (2m^2 - 16) X + m^4),
  hence the same order-4 recurrence.
* `init`: the first four values agree (polynomial identities in m).
* `odd_square`: a(m, 2n+1) = y(m, n)^2 for all m, n.
* `data`: a(3, 0..9) equals the first ten terms of A113249, and `main`.
Not checked here: nothing (the entry's sequence is a(3, n) with the same offset 0).
-/

/-- The family a(m, n): a(m,n) = m^4 a(n-4) + (2m)^2 a(n-3) - 4 a(n-1). -/
def a (m : Int) : Nat → Int
  | 0 => -1
  | 1 => 4
  | 2 => -13 + 6 * (m - 1) + 3 * (m - 1) ^ 2
  | 3 => (m ^ 2 - 8) ^ 2
  | n + 4 => m ^ 4 * a m n + (2 * m) ^ 2 * a m (n + 1) - 4 * a m (n + 3)

/-- y(n) = 4 y(n-1) - m^2 y(n-2), y(0) = 2, y(1) = 8 - m^2. -/
def y (m : Int) : Nat → Int
  | 0 => 2
  | 1 => 8 - m ^ 2
  | n + 2 => 4 * y m (n + 1) - m ^ 2 * y m n

theorem a_rec (m : Int) (k : Nat) :
    a m (k + 4) = m ^ 4 * a m k + (2 * m) ^ 2 * a m (k + 1) - 4 * a m (k + 3) := by
  simp only [a]

theorem y_rec (m : Int) (k : Nat) : y m (k + 2) = 4 * y m (k + 1) - m ^ 2 * y m k := by
  simp only [y]

/-- The odd terms satisfy the order-4 recurrence with characteristic polynomial
    (X - m^2)^2 (X^2 + (2m^2 - 16) X + m^4). -/
theorem odd_rec (m : Int) (n : Nat) :
    a m (2 * n + 9) = 16 * a m (2 * n + 7) - (32 * m ^ 2 - 2 * m ^ 4) * a m (2 * n + 5)
      + 16 * m ^ 4 * a m (2 * n + 3) - m ^ 8 * a m (2 * n + 1) := by
  have r5 : a m (2 * n + 5) = m ^ 4 * a m (2 * n + 1) + (2 * m) ^ 2 * a m (2 * n + 2)
      - 4 * a m (2 * n + 4) := a_rec m (2 * n + 1)
  have r6 : a m (2 * n + 6) = m ^ 4 * a m (2 * n + 2) + (2 * m) ^ 2 * a m (2 * n + 3)
      - 4 * a m (2 * n + 5) := a_rec m (2 * n + 2)
  have r7 : a m (2 * n + 7) = m ^ 4 * a m (2 * n + 3) + (2 * m) ^ 2 * a m (2 * n + 4)
      - 4 * a m (2 * n + 6) := a_rec m (2 * n + 3)
  have r8 : a m (2 * n + 8) = m ^ 4 * a m (2 * n + 4) + (2 * m) ^ 2 * a m (2 * n + 5)
      - 4 * a m (2 * n + 7) := a_rec m (2 * n + 4)
  have r9 : a m (2 * n + 9) = m ^ 4 * a m (2 * n + 5) + (2 * m) ^ 2 * a m (2 * n + 6)
      - 4 * a m (2 * n + 8) := a_rec m (2 * n + 5)
  rw [r9, r8, r7, r6, r5]
  grind

/-- y^2 satisfies the order-3 recurrence (X - m^2)(X^2 + (2m^2 - 16) X + m^4). -/
theorem sq_rec3 (m : Int) (n : Nat) :
    y m (n + 3) ^ 2 = (16 - m ^ 2) * y m (n + 2) ^ 2 + (m ^ 4 - 16 * m ^ 2) * y m (n + 1) ^ 2
      + m ^ 6 * y m n ^ 2 := by
  have r2 : y m (n + 2) = 4 * y m (n + 1) - m ^ 2 * y m n := y_rec m n
  have r3 : y m (n + 3) = 4 * y m (n + 2) - m ^ 2 * y m (n + 1) := y_rec m (n + 1)
  rw [r3, r2]
  grind

/-- hence y^2 also satisfies the order-4 recurrence of the odd terms. -/
theorem sq_rec4 (m : Int) (n : Nat) :
    y m (n + 4) ^ 2 = 16 * y m (n + 3) ^ 2 - (32 * m ^ 2 - 2 * m ^ 4) * y m (n + 2) ^ 2
      + 16 * m ^ 4 * y m (n + 1) ^ 2 - m ^ 8 * y m n ^ 2 := by
  have h0 := sq_rec3 m n
  have h1 := sq_rec3 m (n + 1)
  rw [h1, h0]
  grind

theorem init (m : Int) : a m 1 = y m 0 ^ 2 ∧ a m 3 = y m 1 ^ 2 ∧
    a m 5 = y m 2 ^ 2 ∧ a m 7 = y m 3 ^ 2 := by
  simp only [a, y]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- a(m, 2n+1) = y(m, n)^2 for every integer m and every n. -/
theorem odd_square (m : Int) : ∀ n, a m (2 * n + 1) = y m n ^ 2
  | 0 => (init m).1
  | 1 => (init m).2.1
  | 2 => (init m).2.2.1
  | 3 => (init m).2.2.2
  | n + 4 => by
    have e : 2 * (n + 4) + 1 = 2 * n + 9 := by omega
    rw [e, odd_rec, sq_rec4]
    have h3 := odd_square m (n + 3)
    have h2 := odd_square m (n + 2)
    have h1 := odd_square m (n + 1)
    have h0 := odd_square m n
    rw [show 2 * (n + 3) + 1 = 2 * n + 7 by omega] at h3
    rw [show 2 * (n + 2) + 1 = 2 * n + 5 by omega] at h2
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega] at h1
    rw [h3, h2, h1, h0]

theorem data : (List.range 10).map (a 3) = [-1, 4, 11, 1, 59, 484, -1009, 6241, -2761, 13924] := by decide

theorem main (n : Nat) : ∃ k : Int, a 3 (2 * n + 1) = k ^ 2 := ⟨y 3 n, odd_square 3 n⟩
