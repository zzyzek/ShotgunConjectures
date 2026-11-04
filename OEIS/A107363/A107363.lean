/-
OEIS A107363: expansion of (1-x)(1+x)^2(1+x^2)(1-x^2+2x^3+x^4) /
((1-x^2-x^4)(1+x^2+2x^4-x^6+x^8)).  Conjectures (C. Dement, 2005):
{Fib(n)} = {a(n) : a(n) ≥ 0} = {a(n) : n ≢ 2 (mod 6)} (n ≥ 0).  True.

Checked here (core Lean):
* `den_eq`: the denominator multiplies out to 1 - 4x^6 - x^12, and `num_eq`:
  the numerator is a polynomial of degree 9.  So the coefficients satisfy
  a(n+12) = 4 a(n+6) + a(n) with a(0..11) = N_k + 4 N_{k-6}; `init` checks these
  12 values from the numerator.  `a` below is defined by that recurrence.
* `sections`: a(6j) = F(3j+2), a(6j+1) = F(3j+1), a(6j+2) = -L(3j+1),
  a(6j+3) = F(3j+1), a(6j+4) = F(3j+3), a(6j+5) = 0 (F Fibonacci, L Lucas).
* `nonneg_iff`, `fib_of`, `all_fib`: a(n) ≥ 0 iff n ≢ 2 (mod 6); those terms
  are Fibonacci numbers; every Fibonacci number occurs among them.
Not checked here: the routine step from the g.f. (with the checked numerator
and denominator) to the recurrence with these initial values.
-/

def padd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => (x + y) :: padd p q

def pmul : List Int → List Int → List Int
  | [], _ => []
  | x :: p, q => padd (q.map (x * ·)) (0 :: pmul p q)

def N : List Int := pmul (pmul (pmul (pmul [1, -1] [1, 1]) [1, 1]) [1, 0, 1]) [1, 0, -1, 2, 1]

theorem den_eq : pmul [1, 0, -1, 0, -1] [1, 0, 1, 0, 2, 0, -1, 0, 1] =
    [1, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -1] := by decide
theorem num_eq : N = [1, 1, -1, 1, 2, 0, 1, -1, -3, -1] := by decide

def a : Nat → Int
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => 1 | 4 => 2 | 5 => 0
  | 6 => 5 | 7 => 3 | 8 => -7 | 9 => 3 | 10 => 8 | 11 => 0
  | n + 12 => 4 * a (n + 6) + a n

theorem init : (List.range 12).map a =
    (List.range 12).map (fun k => N.getD k 0 + (if 6 ≤ k then 4 * N.getD (k - 6) 0 else 0)) := by
  decide

def F : Nat → Int
  | 0 => 0 | 1 => 1
  | n + 2 => F (n + 1) + F n

def L : Nat → Int
  | 0 => 2 | 1 => 1
  | n + 2 => L (n + 1) + L n

theorem a_rec (n : Nat) : a (n + 12) = 4 * a (n + 6) + a n := by simp only [a]
theorem F_rec (n : Nat) : F (n + 2) = F (n + 1) + F n := by simp only [F]
theorem L_rec (n : Nat) : L (n + 2) = L (n + 1) + L n := by simp only [L]

theorem F_six (k : Nat) : F (k + 6) = 4 * F (k + 3) + F k := by
  have h2 : F (k + 2) = F (k + 1) + F k := F_rec k
  have h3 : F (k + 3) = F (k + 2) + F (k + 1) := F_rec (k + 1)
  have h4 : F (k + 4) = F (k + 3) + F (k + 2) := F_rec (k + 2)
  have h5 : F (k + 5) = F (k + 4) + F (k + 3) := F_rec (k + 3)
  have h6 : F (k + 6) = F (k + 5) + F (k + 4) := F_rec (k + 4)
  omega

theorem L_six (k : Nat) : L (k + 6) = 4 * L (k + 3) + L k := by
  have h2 : L (k + 2) = L (k + 1) + L k := L_rec k
  have h3 : L (k + 3) = L (k + 2) + L (k + 1) := L_rec (k + 1)
  have h4 : L (k + 4) = L (k + 3) + L (k + 2) := L_rec (k + 2)
  have h5 : L (k + 5) = L (k + 4) + L (k + 3) := L_rec (k + 3)
  have h6 : L (k + 6) = L (k + 5) + L (k + 4) := L_rec (k + 4)
  omega

theorem F_nonneg : ∀ n, 0 ≤ F n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by rw [F_rec]; have := F_nonneg (n + 1); have := F_nonneg n; omega

theorem L_pos : ∀ n, 0 < L n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by rw [L_rec]; have := L_pos (n + 1); have := L_pos n; omega

def S (j : Nat) : Prop :=
  a (6 * j) = F (3 * j + 2) ∧ a (6 * j + 1) = F (3 * j + 1) ∧ a (6 * j + 2) = -L (3 * j + 1) ∧
  a (6 * j + 3) = F (3 * j + 1) ∧ a (6 * j + 4) = F (3 * j + 3) ∧ a (6 * j + 5) = 0

theorem sections : ∀ j, S j
  | 0 => by unfold S; decide
  | 1 => by unfold S; decide
  | j + 2 => by
    have h1 := sections (j + 1)
    have h0 := sections j
    unfold S at *
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h1
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h0
    have r : ∀ r, a (6 * (j + 2) + r) = 4 * a (6 * (j + 1) + r) + a (6 * j + r) := by
      intro r
      rw [show 6 * (j + 2) + r = (6 * j + r) + 12 by omega,
          show 6 * (j + 1) + r = (6 * j + r) + 6 by omega]
      exact a_rec (6 * j + r)
    have f : ∀ c, F (3 * (j + 2) + c) = 4 * F (3 * (j + 1) + c) + F (3 * j + c) := by
      intro c
      rw [show 3 * (j + 2) + c = (3 * j + c) + 6 by omega,
          show 3 * (j + 1) + c = (3 * j + c) + 3 by omega]
      exact F_six (3 * j + c)
    have l : ∀ c, L (3 * (j + 2) + c) = 4 * L (3 * (j + 1) + c) + L (3 * j + c) := by
      intro c
      rw [show 3 * (j + 2) + c = (3 * j + c) + 6 by omega,
          show 3 * (j + 1) + c = (3 * j + c) + 3 by omega]
      exact L_six (3 * j + c)
    have r0 := r 0; have r1 := r 1; have r2 := r 2; have r3 := r 3; have r4 := r 4; have r5 := r 5
    have f1 := f 1; have f2 := f 2; have f3 := f 3; have l1 := l 1
    simp only [Nat.add_zero] at r0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem nonneg_iff (n : Nat) : 0 ≤ a n ↔ n % 6 ≠ 2 := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := sections (n / 6)
  have hn : n = 6 * (n / 6) + n % 6 := by omega
  have := F_nonneg (3 * (n / 6) + 2); have := F_nonneg (3 * (n / 6) + 1)
  have := F_nonneg (3 * (n / 6) + 3); have := L_pos (3 * (n / 6) + 1)
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize n / 6 = q at *
  generalize n % 6 = r at *
  subst hn
  match r, h6 with
  | 0, _ => simp only [Nat.add_zero]; omega
  | 1, _ => omega | 2, _ => omega | 3, _ => omega | 4, _ => omega | 5, _ => omega

theorem fib_of (n : Nat) (h : n % 6 ≠ 2) : ∃ i, a n = F i := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := sections (n / 6)
  have hn : n = 6 * (n / 6) + n % 6 := by omega
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize n / 6 = q at *
  generalize n % 6 = r at *
  subst hn
  match r, h6 with
  | 0, _ => exact ⟨_, a0⟩
  | 1, _ => exact ⟨_, a1⟩
  | 2, _ => exact absurd rfl h
  | 3, _ => exact ⟨_, a3⟩
  | 4, _ => exact ⟨_, a4⟩
  | 5, _ => exact ⟨0, by rw [a5]; decide⟩

theorem all_fib (i : Nat) : ∃ n, n % 6 ≠ 2 ∧ a n = F i := by
  obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, i = 3 * q ∨ i = 3 * q + 1 ∨ i = 3 * q + 2 := ⟨i / 3, by omega⟩
  · cases q with
    | zero => exact ⟨5, by decide, by decide⟩
    | succ q =>
      refine ⟨6 * q + 4, by omega, ?_⟩
      rw [(sections q).2.2.2.2.1, show 3 * (q + 1) = 3 * q + 3 by omega]
  · exact ⟨6 * q + 1, by omega, (sections q).2.1⟩
  · exact ⟨6 * q, by omega, (sections q).1⟩
