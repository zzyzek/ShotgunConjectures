/-
NT-B31.5 (Guy, UPINT 3rd ed., B31, Erdős–Szekeres): "is the greatest prime
factor of gcd(C(n,r), C(n,s)), 0 < r < s ≤ n/2, always greater than r?"
No; the book itself quotes n = 28, r = 5, s = 14.

Checked here (core Lean, no Mathlib; `decide`):
* `b31_5`: gcd(C(28,5), C(28,14)) = 1080 = 2^3·3^3·5, whose greatest prime
  factor 5 is not greater than r = 5.  Smaller counterexamples with r ≤ 3:
  (n, r, s) = (10, 3, 5) gcd 12, (16, 2, 6) gcd 8, (28, 3, 14) gcd 36.
Not checked here: nothing else is claimed.
-/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def choose' (n k : Nat) : Nat := fact n / (fact k * fact (n - k))

theorem b31_5 : Nat.gcd (choose' 28 5) (choose' 28 14) = 1080 ∧ 1080 = 2 ^ 3 * 3 ^ 3 * 5 := by decide
theorem b31_5_small :
    Nat.gcd (choose' 10 3) (choose' 10 5) = 12 ∧ Nat.gcd (choose' 16 2) (choose' 16 6) = 8 ∧
    Nat.gcd (choose' 28 3) (choose' 28 14) = 36 := by decide
