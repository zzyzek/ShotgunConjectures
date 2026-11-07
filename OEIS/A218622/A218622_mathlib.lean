import Mathlib
import OpenProblemsLib.HannaMod4

/-!
# OEIS A218622: a(n) = A183161(n) mod 4 never equals 3

A218622 (Hanna): a(n) = A183161(n) mod 4, where A183161 is the integer sequence with
A183161(0) = 1 whose self-convolution is A183160(n) = sum_{k=0..n} C(n+k, n-k) C(2n-k, k).
Conjecture: a(n) never equals 3.

Checked here.
* `A183161_spec`, `A183161_unique`: the integer sequence `OpenProblemsLib.HannaMod4.A183161`
  has value 1 at 0 and self-convolution A183160, and it is the only one.
* `A218622_ne_three`: A218622(n) = A183161(n) mod 4 ≠ 3 for all n.
* `A218622_ne_three_of_conv`: for every integer sequence b with b(0) = 1 and self-convolution
  A183160, b(n) mod 4 ≠ 3 for all n (`OpenProblemsLib.HannaMod4.A183161_def_mod4`; Lagrange
  inversion, then a six-state automaton modulo 4 built with `OpenProblemsLib.AutomaticMod`).
The printed OEIS terms are not used in Lean; they agree with the definition for the 60 cached
terms (OEIS/A183161/certificate/rootseq_check.py).
-/

/-- A183161, the integer self-convolution square root of A183160. -/
noncomputable abbrev A183161 : ℕ → ℤ := OpenProblemsLib.HannaMod4.A183161

/-- A218622(n) = A183161(n) mod 4. -/
noncomputable def A218622 (n : ℕ) : ℤ := A183161 n % 4

theorem A183161_spec : A183161 0 = 1 ∧ ∀ n, ∑ k ∈ Finset.range (n + 1), A183161 k * A183161 (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ) :=
  OpenProblemsLib.HannaMod4.A183161_spec

theorem A183161_unique (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ)) :
    a = A183161 :=
  OpenProblemsLib.HannaMod4.A183161_unique a h0 hconv

theorem A218622_ne_three (n : ℕ) : A218622 n ≠ 3 :=
  OpenProblemsLib.HannaMod4.A183161_ne_three n

theorem A218622_ne_three_of_conv (b : ℕ → ℤ) (h0 : b 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), b k * b (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ))
    (n : ℕ) : b n % 4 ≠ 3 :=
  OpenProblemsLib.HannaMod4.A183161_def_mod4 b h0
    (fun n => by rw [hconv n, OpenProblemsLib.HannaMod4.A183160]) n
