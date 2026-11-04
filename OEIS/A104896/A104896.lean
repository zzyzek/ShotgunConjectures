/-
OEIS A104896: a(0) = 0, a(n) = 7 a(n-1) + 7.  Conjecture: a(n) is the number of
integers in [0, 10^n) with no digit 0, 1 or 2.  True (trivial): such integers
are the nonempty strings of length ≤ n over {3, ..., 9}, 7 + 7^2 + ... + 7^n.

Checked here (core Lean):
* `closed`: 6 a(n) + 7 = 7^(n+1), and `sum_eq`: 6 (7 + ... + 7^n) + 7 = 7^(n+1),
  so a(n) = 7 + ... + 7^n.
* `count3`: the direct count for n = 3 is 399 = a(3).
Not checked here: the positional-notation bijection.
-/

def a : Nat → Nat
  | 0 => 0
  | n + 1 => 7 * a n + 7

def s : Nat → Nat
  | 0 => 0
  | n + 1 => s n + 7 ^ (n + 1)

theorem closed (n : Nat) : 6 * a n + 7 = 7 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    simp only [a]
    have h : 7 ^ (k + 1 + 1) = 7 ^ (k + 1) * 7 := by rw [Nat.pow_succ]
    omega

theorem sum_eq (n : Nat) : 6 * s n + 7 = 7 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    simp only [s]
    have h : 7 ^ (k + 1 + 1) = 7 ^ (k + 1) * 7 := by rw [Nat.pow_succ]
    omega

theorem a_eq_s (n : Nat) : a n = s n := by
  have h1 := closed n
  have h2 := sum_eq n
  omega

/-- all decimal digits of x lie in {3,...,9} (x > 0, at most 4 digits). -/
def good : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, x => decide (3 ≤ x % 10) && (x / 10 == 0 || good f (x / 10))

theorem count3 : ((List.range 10).map (fun i =>
    ((List.range 100).filter (fun j => good 4 (100 * i + j))).length)).sum = 399 ∧ a 3 = 399 := by
  decide
