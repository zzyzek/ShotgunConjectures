/-
OEIS A129454: a(n) = prod_{i,j,k=1..n-1} gcd(i,j,k) (offset 0).
Conjecture: v_p(a(n)) = sum_t floor(n/p^t)^3. As printed this is off by one;
the true statement is v_p(a(n)) = sum_t floor((n-1)/p^t)^3.

Checked here (core Lean, `decide`): a(n) for n ≤ 6 computed from the
definition; the shifted formula for p = 2, 3, 5 and n ≤ 6; and the literal
formula failing at n = 3, p = 3 (a(3) = 2, formula gives v_3 = 1).
Not checked here: the general double-counting identity
sum_{i,j,k ≤ N} v_p(gcd(i,j,k)) = sum_t floor(N/p^t)^3 (see README).
-/

def a (n : Nat) : Nat :=
  ((List.range (n - 1)).map fun i => ((List.range (n - 1)).map fun j =>
    ((List.range (n - 1)).map fun k => Nat.gcd (Nat.gcd (i + 1) (j + 1)) (k + 1)).foldl (· * ·) 1).foldl (· * ·) 1).foldl (· * ·) 1

/-- p-adic valuation with fuel. -/
def v (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, x => if x ≠ 0 ∧ x % p = 0 then 1 + v p f (x / p) else 0

def form (N p : Nat) : Nat := (List.range 4).foldl (fun s t => s + (N / p ^ (t + 1)) ^ 3) 0

theorem values : (List.range 7).map a = [1, 1, 1, 2, 6, 1536, 7680] := by decide
theorem shifted : (List.range 6).all (fun i =>
    [2, 3, 5].all (fun p => v p 20 (a (i + 1)) == form i p)) = true := by decide
theorem literal_fails : v 3 20 (a 3) = 0 ∧ form 3 3 = 1 := by decide
