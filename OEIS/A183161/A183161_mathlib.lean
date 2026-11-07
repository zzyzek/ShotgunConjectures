import Mathlib
import OpenProblemsLib.HannaMod4

/-!
# OEIS A183161: no term is 3 (mod 4)

A183161 (Hanna): a(0) = 1 and the self-convolution of a is A183160,
  sum_{k=0..n} a(k) a(n-k) = A183160(n) = sum_{k=0..n} C(n+k, n-k) C(2n-k, k).
Conjecture (Hanna, 2012): a(n) is never 3 (mod 4).

Checked here.
* `A183161_spec`, `A183161_unique`: the integer sequence `A183161` (defined in the library as
  [tⁿ] R(t)(1-3t)(1-t)^(-2n-1), R = 1/sqrt((1-3t)(1+t)), an integer series via Catalan numbers)
  has A183161(0) = 1 and self-convolution A183160, and it is the only integer sequence with these
  two properties.
* `A183161_mod4`: A183161(n) mod 4 ≠ 3 for all n.
* `A183161_mod4_of_conv`: every integer sequence a with a(0) = 1 and self-convolution A183160 has
  a(n) mod 4 ≠ 3 for all n (`OpenProblemsLib.HannaMod4.A183161_def_mod4`).
* `A183161_gf_mod4`: the same for the coefficients of Hanna's g.f. A = 1/sqrt(1 - 2xG^2 - 3x^2G^4),
  G = 1 + xG^3 (`OpenProblemsLib.HannaMod4.gf_mod4`).
Proof (in the library): Lagrange inversion for x = t(1-t)^2 turns a(n) into
[t^n] S(t) (1-t)^(-2n-1) with S = sqrt((1-3t)/(1+t)); S = 1 + 2W (mod 4) with W lacunary; the
diagonal of (1+2W)(1-t)/((1-t)^2 - x) mod 4 is computed by a six-state Rowland-Yassawi automaton
(`OpenProblemsLib.AutomaticMod`), whose outputs are 0, 1, 2.
The printed OEIS terms are not used in Lean; they agree with the definition for the 24 cached
terms (certificate/rootseq_check.py).
-/

open PowerSeries

/-- A183161, the integer self-convolution square root of A183160. -/
noncomputable abbrev A183161 : ℕ → ℤ := OpenProblemsLib.HannaMod4.A183161

theorem A183161_spec : A183161 0 = 1 ∧ ∀ n, ∑ k ∈ Finset.range (n + 1), A183161 k * A183161 (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ) :=
  OpenProblemsLib.HannaMod4.A183161_spec

theorem A183161_unique (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ)) :
    a = A183161 :=
  OpenProblemsLib.HannaMod4.A183161_unique a h0 hconv

theorem A183161_mod4 (n : ℕ) : A183161 n % 4 ≠ 3 :=
  OpenProblemsLib.HannaMod4.A183161_ne_three n

theorem A183161_mod4_of_conv (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ))
    (n : ℕ) : a n % 4 ≠ 3 :=
  OpenProblemsLib.HannaMod4.A183161_def_mod4 a h0
    (fun n => by rw [hconv n, OpenProblemsLib.HannaMod4.A183160]) n

theorem A183161_gf_mod4 (G A : ℤ⟦X⟧) (hG : G = 1 + X * G ^ 3) (hA0 : constantCoeff A = 1)
    (hA : A ^ 2 * (1 - 2 * X * G ^ 2 - 3 * X ^ 2 * G ^ 4) = 1) (n : ℕ) :
    coeff n A % 4 ≠ 3 := by
  have h := OpenProblemsLib.HannaMod4.gf_mod4 G A hG hA0 hA 0 (by omega) n
  rwa [pow_zero, one_mul] at h
