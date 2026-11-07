import Mathlib
import OpenProblemsLib.HannaMod4

/-!
# OEIS A183161: no term is 3 (mod 4)

A183161 (Hanna): a(0) = 1 and the self-convolution of a is A183160,
  sum_{k=0..n} a(k) a(n-k) = A183160(n) = sum_{k=0..n} C(n+k, n-k) C(2n-k, k).
Conjecture (Hanna, 2012): a(n) is never 3 (mod 4).

Checked here.
* `A183161_mod4`: every integer sequence a with a(0) = 1 and self-convolution A183160 has
  a(n) mod 4 ≠ 3 for all n (`OpenProblemsLib.HannaMod4.A183161_def_mod4`).
* `A183161_gf_mod4`: the same for the coefficients of Hanna's g.f. A = 1/sqrt(1 - 2xG^2 - 3x^2G^4),
  G = 1 + xG^3 (`OpenProblemsLib.HannaMod4.gf_mod4`).
Proof (in the library): Lagrange inversion for x = t(1-t)^2 turns a(n) into
[t^n] S(t) (1-t)^(-2n-1) with S = sqrt((1-3t)/(1+t)); S = 1 + 2W (mod 4) with W lacunary; the
diagonal of (1+2W)(1-t)/((1-t)^2 - x) mod 4 is computed by a six-state Rowland-Yassawi automaton
(`OpenProblemsLib.AutomaticMod`), whose outputs are 0, 1, 2.
Not checked: that an integer sequence with these properties exists (the OEIS terms are one).
-/

open PowerSeries

theorem A183161_mod4 (a : ℕ → ℤ) (h0 : a 0 = 1)
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
