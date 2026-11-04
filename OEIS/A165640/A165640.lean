/-
OEIS A165640: number of multisets of n integers from {-2, 1, 3} with sum 3.
Conjecture: a(n) = floor(4(n+4)/5) - floor(2(n+4)/3) (n ≥ 1).

Argument (quasi-polynomial, METHODS §6). With x, y, z the multiplicities of
-2, 1, 3: y = n - x - z and 3x = n - 3 + 2z, so a(n) counts z with
z ≡ n (mod 3) in an interval [max(0, (3-n)/2), (2n+3)/5]. For n ≥ 3 this is a
quasi-polynomial in n of degree 1 with period 15 (lcm of 5 and 3); so is the
floor formula. Two such quasi-polynomials agreeing on 2 full periods
(30 consecutive n ≥ 3) agree for all n ≥ 3.

Checked here (core Lean, `decide`): the brute-force count equals the formula
for 1 ≤ n ≤ 60 (four periods).
Not checked here: the quasi-polynomial structure of the count (the
interval description above), which turns the finite check into a proof.
-/

def count (n : Nat) : Nat :=
  ((List.range (n + 1)).map (fun x =>
    ((List.range (n + 1 - x)).filter (fun z =>
      decide (2 * x + 3 = (n - x - z) + 3 * z))).length)).foldl (· + ·) 0

def formula (n : Nat) : Nat := (4 * (n + 4)) / 5 - (2 * (n + 4)) / 3

theorem agree1 : (List.range 15).all (fun i => count (i + 1) == formula (i + 1)) = true := by decide
theorem agree2 : (List.range 15).all (fun i => count (i + 16) == formula (i + 16)) = true := by decide
theorem agree3 : (List.range 15).all (fun i => count (i + 31) == formula (i + 31)) = true := by decide
theorem agree4 : (List.range 15).all (fun i => count (i + 46) == formula (i + 46)) = true := by decide
