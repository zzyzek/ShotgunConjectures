/-
OEIS A106249: expansion of (1-x+x^2+x^3)/((1+x)(1+x^2)(1-x)^2), offset 0.
Conjecture (M. Lagneau, 2012): number of roots of x^n + 1 in the left
half-plane, n > 0.  Literally off by one (a(1) = 0, but x + 1 has the root -1);
true with the shift a(n) = #{roots of x^(n+1) + 1 with negative real part}.

The roots of x^m + 1 are exp(iπ(2k+1)/m), 0 ≤ k < m; the real part is
negative iff π/2 < π(2k+1)/m < 3π/2, i.e. m < 2(2k+1) < 3m.

Checked here (core Lean):
* `den_eq`: (1+x)(1+x^2)(1-x)^2 = 1 - x - x^4 + x^5, so a(n+5) = a(n+4) + a(n+1)
  - a(n) with a(0..4) = 1, 0, 1, 2, 3 (`init` from the numerator).
* `closed`: a(n) = 2·⌊(n+1)/4⌋ + ((n+1) mod 2) for all n.
* `count_small`: #{k < m : m < 2(2k+1) < 3m} = 2·⌊m/4⌋ + (m mod 2) for m < 64.
Not checked here: the cosine sign condition above, the count formula for
m ≥ 64 (it is the number of odd integers in (m/2, 3m/2), period 4 in m), and
the routine step from the g.f. to the recurrence.
-/

def padd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => (x + y) :: padd p q

def pmul : List Int → List Int → List Int
  | [], _ => []
  | x :: p, q => padd (q.map (x * ·)) (0 :: pmul p q)

theorem den_eq : pmul (pmul (pmul [1, 1] [1, 0, 1]) [1, -1]) [1, -1] = [1, -1, 0, 0, -1, 1] := by
  decide

def a : Nat → Int
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3
  | n + 5 => a (n + 4) + a (n + 1) - a n

/-- series coefficients of (1 - x + x^2 + x^3)/(1 - x - x^4 + x^5) for k < 5. -/
theorem init : (a 0, a 1, a 2, a 3, a 4) = (1, -1 + 1, 1 + (-1 + 1), 1 + (1 + (-1 + 1)), 0 + 2 + 1) := by
  decide

def C (m : Nat) : Int := 2 * ((m : Int) / 4) + (m : Int) % 2

theorem C_rec (n : Nat) : C (n + 6) = C (n + 5) + C (n + 2) - C (n + 1) := by
  unfold C
  have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h with h | h | h | h <;> omega

theorem closed : ∀ n, a n = C (n + 1)
  | 0 => by decide | 1 => by decide | 2 => by decide | 3 => by decide | 4 => by decide
  | n + 5 => by
    rw [show a (n + 5) = a (n + 4) + a (n + 1) - a n by simp only [a], closed (n + 4),
      closed (n + 1), closed n, C_rec n]

def count (m : Nat) : Nat := ((List.range m).filter (fun k => m < 2 * (2 * k + 1) && 2 * (2 * k + 1) < 3 * m)).length

theorem count_small : ∀ m, m < 64 → (count m : Int) = C m := by decide
