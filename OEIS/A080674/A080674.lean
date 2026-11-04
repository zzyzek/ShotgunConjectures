/-
OEIS A080674: a(n) = (4/3)(4^n - 1).  Conjecture (A. Wajnberg, 2005): a(n) is
the number of integers in [0, 10^n) with no digit in {0, 1, 2, 3, 4, 5}.
True (trivial): such integers are the k-digit strings over {6, 7, 8, 9},
k = 1..n (0 itself has the digit 0), so the count is 4 + 4^2 + ... + 4^n.

Checked here (core Lean):
* `sum_eq`: 3·(4 + 4^2 + ... + 4^n) = 4·(4^n - 1) for all n.
* `count3`: the direct count for n = 3 is 84 = a(3).
Not checked here: the bijection between such integers and nonempty strings
of length ≤ n over {6, 7, 8, 9} (standard positional notation).
-/

def s : Nat → Nat
  | 0 => 0
  | n + 1 => s n + 4 ^ (n + 1)

theorem sum_eq (n : Nat) : 3 * s n + 4 = 4 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    simp only [s]
    have h : 4 ^ (k + 1 + 1) = 4 ^ (k + 1) * 4 := by rw [Nat.pow_succ]
    omega

/-- all decimal digits of x lie in {6,7,8,9} (x > 0, at most 4 digits). -/
def good : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, x => decide (6 ≤ x % 10) && (x / 10 == 0 || good f (x / 10))

theorem count3 : ((List.range 10).map (fun i =>
    ((List.range 100).filter (fun j => good 4 (100 * i + j))).length)).sum = 84 ∧
    4 * (4 ^ 3 - 1) / 3 = 84 := by decide
