/-
OEIS A214449: least m > 0 with n! ≤ m^m (offset 1). Conjecture: A214449 is
A118168 (x minimizing |x^x - n!|, offset 0: 1, 1, 1, 2, 3, ...) with the
first two 1s deleted, i.e. A214449(n) = A118168(n+1) for n ≥ 1. False: the
first mismatch is n = 188.

A214449(188) = 159 because 158^158 < 188! ≤ 159^159.
A118168(189) = 158 because 158^158 < 189! < 159^159 and 189! is nearer to
158^158 (x^x is increasing, so the minimizer is one of the two neighbours).

Checked here (core Lean, `decide +kernel`, big-number arithmetic is
kernel-accelerated): the four inequalities and the nearness comparison.
Not checked here: monotonicity of x ↦ x^x (used to restrict to neighbours),
and that 188 is the first mismatch (certificate script).
-/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem a214449_188 : 158 ^ 158 < fact 188 ∧ fact 188 ≤ 159 ^ 159 := by decide +kernel
theorem a118168_189 : 158 ^ 158 < fact 189 ∧ fact 189 < 159 ^ 159 ∧
    fact 189 - 158 ^ 158 < 159 ^ 159 - fact 189 := by decide +kernel
