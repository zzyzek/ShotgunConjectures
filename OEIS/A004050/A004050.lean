/-
OEIS A004050 (numbers 2^j + 3^k) / A085634. Conjecture (OEIS wiki
Talk:Conjectures/List, A004050 line 46): only 5, 11, 17, 35, 259 have two
representations, i.e. 2^a + 3^b = 2^c + 3^d with a > c forces the value to
be one of these.  True, given Ellison (1971).

Argument (README): with a > c one gets d > b, d ≤ a and
|2^a - 3^d| = |2^c - 3^b| ≤ max(2^c, 3^b) ≤ 4a (2-adic and 3-adic
valuations, lifting the exponent).  Ellison: |2^x - 3^y| > 2^x e^(-x/10) for
x ≥ 12, x ∉ {13, 14, 16, 19, 27}, which exceeds 4x, so a ≤ 27.

Checked here (core Lean, `decide`):
* `pairs`: for X, Y ≤ 27, |2^X - 3^Y| ≤ 4X only for the 16 listed pairs.
* `sols`: for each listed pair (a, d) and all b < d, c < a, a solution of
  2^a + 3^b = 2^c + 3^d has value in {5, 11, 17, 35, 259}.
* `reps`: each of the five values has two representations with a > c.
Not checked here: the reduction to |2^a - 3^d| ≤ 4a, d ≤ a (valuation
argument, README) and Ellison's bound (a ≤ 27), a literature result quoted
from Waldschmidt, arXiv:0908.4031.
-/

def absDiff (x y : Nat) : Nat := (x - y) + (y - x)

def small : List (Nat × Nat) :=
  [(0,0), (1,0), (1,1), (2,0), (2,1), (2,2), (3,0), (3,1), (3,2), (4,0), (4,1),
   (4,2), (4,3), (5,3), (6,4), (8,5)]

theorem pairs : (List.range 28).all (fun X => (List.range 28).all (fun Y =>
    !(absDiff (2 ^ X) (3 ^ Y) ≤ 4 * X) || small.contains (X, Y))) = true := by decide

theorem sols : small.all (fun p => (List.range p.2).all (fun b =>
    (List.range p.1).all (fun c =>
      !(2 ^ p.1 + 3 ^ b == 2 ^ c + 3 ^ p.2) ||
      [5, 11, 17, 35, 259].contains (2 ^ p.1 + 3 ^ b)))) = true := by decide

theorem reps : 2^2 + 3^0 = 2^1 + 3^1 ∧ 2^3 + 3^1 = 2^1 + 3^2 ∧ 2^4 + 3^0 = 2^3 + 3^2 ∧
    2^5 + 3^1 = 2^3 + 3^3 ∧ 2^8 + 3^1 = 2^4 + 3^5 := by decide
