/-
OEIS A008676: expansion of 1/((1-x^3)(1-x^5)).  Conjecture (J. W. Layman,
2009): a(n) = floor(2(n+3)/3) - floor(3(n+3)/5).  True.

`a` below is the g.f. written as its recurrence: multiplying out,
(1 - x^3 - x^5 + x^8) A(x) = 1, so a(n) = a(n-3) + a(n-5) - a(n-8) for n ≥ 8
with a(0..7) = 1,0,0,1,0,1,1,0 (the first 8 coefficients).

Checked here (core Lean, full statement for the recurrence definition):
* `rhs_rec`: the floor formula satisfies the same recurrence (omega, one
  case per residue of n mod 15).
* `main`: a(n) = formula for all n (8 initial values, then induction).
Not checked here: the routine step from the g.f. to the recurrence above.
-/

def a : Nat → Int
  | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 1 | 6 => 1 | 7 => 0
  | n + 8 => a (n + 5) + a (n + 3) - a n

def rhs (n : Nat) : Int := 2 * ((n : Int) + 3) / 3 - 3 * ((n : Int) + 3) / 5

theorem rhs_rec (n : Nat) : rhs (n + 8) = rhs (n + 5) + rhs (n + 3) - rhs n := by
  unfold rhs
  have h : n % 15 = 0 ∨ n % 15 = 1 ∨ n % 15 = 2 ∨ n % 15 = 3 ∨ n % 15 = 4 ∨
      n % 15 = 5 ∨ n % 15 = 6 ∨ n % 15 = 7 ∨ n % 15 = 8 ∨ n % 15 = 9 ∨
      n % 15 = 10 ∨ n % 15 = 11 ∨ n % 15 = 12 ∨ n % 15 = 13 ∨ n % 15 = 14 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega

theorem main : ∀ n, a n = rhs n
  | 0 => by decide | 1 => by decide | 2 => by decide | 3 => by decide
  | 4 => by decide | 5 => by decide | 6 => by decide | 7 => by decide
  | n + 8 => by rw [a, rhs_rec, main (n + 5), main (n + 3), main n]
