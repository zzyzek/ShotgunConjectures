/-
OEIS A100056 (sum of |differences| of consecutive entries of the A054065
permutation of 1..n).  Conjecture: a(n) is the maximum of this sum over all
permutations of 1..n, attained by the A054065 permutations.  False at n = 5.

Checked here (core Lean, `decide`):
* `row5`: the A054065 permutation for n = 5, (5,2,4,1,3), has sum 10 = a(5).
* `better`: (4,2,5,1,3) is a permutation of 1..5 with sum 11 > 10.
Not checked here: that (5,2,4,1,3) is the A054065 row for n = 5 (ordering
h = 1..5 by the fractional part of h·τ; listed in A054065 and recomputed in
certificate/check.py).
-/

def dsum : List Int → Int
  | x :: y :: t => (if x ≤ y then y - x else x - y) + dsum (y :: t)
  | _ => 0

def isPerm5 (p : List Int) : Bool := p.length == 5 && [1, 2, 3, 4, 5].all (fun i => p.contains i)

theorem row5 : isPerm5 [5, 2, 4, 1, 3] = true ∧ dsum [5, 2, 4, 1, 3] = 10 := by decide
theorem better : isPerm5 [4, 2, 5, 1, 3] = true ∧ dsum [4, 2, 5, 1, 3] = 11 := by decide
