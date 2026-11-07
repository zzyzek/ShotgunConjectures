import Mathlib
import OpenProblemsLib.HannaMod4

/-!
# OEIS A218622: a(n) = A183161(n) mod 4 never equals 3

A218622 (Hanna): a(n) = A183161(n) mod 4, where A183161 is the integer sequence with
A183161(0) = 1 whose self-convolution is A183160(n) = sum_{k=0..n} C(n+k, n-k) C(2n-k, k).
Conjecture: a(n) never equals 3.

Checked here (`A218622_ne_three`): for every integer sequence b with b(0) = 1 and self-convolution
A183160, b(n) mod 4 ≠ 3 for all n (`OpenProblemsLib.HannaMod4.A183161_def_mod4`; Lagrange
inversion, then a six-state automaton modulo 4 built with `OpenProblemsLib.AutomaticMod`).
Not checked: that an integer sequence with these properties exists (the OEIS terms are one).
-/

theorem A218622_ne_three (b : ℕ → ℤ) (h0 : b 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), b k * b (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ))
    (n : ℕ) : b n % 4 ≠ 3 :=
  OpenProblemsLib.HannaMod4.A183161_def_mod4 b h0
    (fun n => by rw [hconv n, OpenProblemsLib.HannaMod4.A183160]) n
