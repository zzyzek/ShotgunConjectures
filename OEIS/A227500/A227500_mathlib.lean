/-
OEIS A227500: (b(n) - a(n))/c(n) = 0, 0, then the Fibonacci numbers (conjecture of P. Curtz, 2013).

Checked here (Mathlib):
* `r B` is the transform of the entry: r(0) = r(1) = 0, r(n+2) = r(n+1) + r(n) + B(n).
* a(n)/c(n) = `r bernoulli n` in lowest terms (Mathlib `bernoulli`, B(1) = -1/2, = A027641/A027642);
  b(n)/c'(n) = `r bernoulli' n` in lowest terms (Mathlib `bernoulli'`, B(1) = +1/2, = A164555/A027642).
* `A227500_diff`: r bernoulli' (n+2) - r bernoulli (n+2) = fib n, and the difference is 0 for n = 0, 1.
* `A227500_den`: both have the same reduced denominator, so c(n) is well defined.
* `A227500_main`: (b(n) - a(n))/c(n) = fib (n-2) for n >= 2, and = 0 for n < 2.
Not checked here: that Mathlib's `bernoulli`/`bernoulli'` match the OEIS numerator/denominator tables
(certificate/check.gp compares the first 200 terms of a(n) with the definition).
-/
import Mathlib

namespace OEIS227500

/-- The transform of the entry applied to a sequence `B`. -/
def r (B : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | n + 2 => r B (n + 1) + r B n + B n

lemma bdiff (n : ℕ) : bernoulli' n - bernoulli n = if n = 1 then 1 else 0 := by
  by_cases h : n = 1
  · subst h; rw [bernoulli'_one, bernoulli_one]; norm_num
  · rw [bernoulli_eq_bernoulli'_of_ne_one h]; simp [h]

lemma diff_pair (n : ℕ) :
    r bernoulli' (n + 2) - r bernoulli (n + 2) = Nat.fib n ∧
      r bernoulli' (n + 3) - r bernoulli (n + 3) = Nat.fib (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [r]
    · have h0 := bdiff 0; have h1 := bdiff 1; simp only [r] at h0 h1 ⊢; simp at h0 h1 ⊢; linarith
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hb := bdiff (n + 2)
    simp only [show n + 2 ≠ 1 by omega, ite_false] at hb
    have e : ∀ B : ℕ → ℚ, r B (n + 1 + 3) = r B (n + 3) + r B (n + 2) + B (n + 2) := fun B => rfl
    rw [e, e, Nat.fib_add_two, Nat.cast_add]
    linarith [ih.1, ih.2]

theorem A227500_diff (n : ℕ) : r bernoulli' (n + 2) - r bernoulli (n + 2) = Nat.fib n :=
  (diff_pair n).1

theorem A227500_diff_small : r bernoulli' 0 - r bernoulli 0 = 0 ∧ r bernoulli' 1 - r bernoulli 1 = 0 := by
  simp [r]

/-- The difference is always an integer (a natural number). -/
lemma diff_nat (n : ℕ) : r bernoulli' n = r bernoulli n + (Nat.fib (n - 2) : ℕ) := by
  rcases n with _ | _ | n
  · simp [r]
  · simp [r]
  · rw [show n + 2 - 2 = n by omega, ← A227500_diff n]; ring

theorem A227500_den (n : ℕ) : (r bernoulli' n).den = (r bernoulli n).den := by
  rw [diff_nat, Rat.add_natCast_den]

/-- The conjecture: with a(n), b(n) the numerators and c(n) the common denominator,
(b(n) - a(n))/c(n) = fib(n-2) for n >= 2 and 0 for n < 2. -/
theorem A227500_main (n : ℕ) :
    (((r bernoulli' n).num - (r bernoulli n).num : ℤ) : ℚ) / (r bernoulli n).den =
      if 2 ≤ n then (Nat.fib (n - 2) : ℚ) else 0 := by
  have hd : ((r bernoulli n).den : ℚ) ≠ 0 := by exact_mod_cast (r bernoulli n).den_nz
  have e1 := Rat.mul_den_eq_num (r bernoulli' n)
  have e2 := Rat.mul_den_eq_num (r bernoulli n)
  rw [A227500_den] at e1
  push_cast
  rw [← e1, ← e2, ← sub_mul, mul_div_assoc, div_self hd, mul_one]
  rcases n with _ | _ | n
  · simp [r]
  · simp [r]
  · rw [A227500_diff n]; simp

end OEIS227500

open OEIS227500
