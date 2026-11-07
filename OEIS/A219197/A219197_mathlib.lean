import Mathlib
import OpenProblemsLib.HannaMod4

/-!
# OEIS A219197: no term is 3 (mod 4)

A219197 (Hanna): the self-convolution square root of A199033(n) = sum_k C(n+k+1, n-k) C(2n-k+1, k).
The entry gives the g.f. A(x) = G(x)/sqrt(1 - 2x G(x)^2 - 3x^2 G(x)^4) with G = 1 + x G^3.
Conjecture: a(n) is never 3 (mod 4).

Checked here.
* `A219197_def_mod4`: every integer sequence a with a(0) = 1 and self-convolution A199033 has
  a(n) mod 4 ≠ 3 for all n (`OpenProblemsLib.HannaMod4.A219197_def_mod4`).
* `A219197_mod4`: the same for the coefficients of any A with G = 1 + X G^3, A(0) = 1 and
  A^2 (1 - 2X G^2 - 3X^2 G^4) = G^2 (Hanna's g.f.); with A₀ = A / G this is
  `OpenProblemsLib.HannaMod4.gf_mod4` for G A₀.
Proof (in the library): Lagrange inversion for x = t(1-t)^2, then a six-state Rowland-Yassawi
automaton over ℤ/4 (`OpenProblemsLib.AutomaticMod`).
Not checked: that an integer sequence with these properties exists (the OEIS terms are one).
-/

open PowerSeries

theorem A219197_def_mod4 (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k + 1).choose (n - k) * (2 * n - k + 1).choose k : ℕ) : ℤ))
    (n : ℕ) : a n % 4 ≠ 3 :=
  OpenProblemsLib.HannaMod4.A219197_def_mod4 a h0
    (fun n => by rw [hconv n, OpenProblemsLib.HannaMod4.A199033]) n

theorem A219197_mod4 (G A : ℤ⟦X⟧) (hG : G = 1 + X * G ^ 3) (hA0 : constantCoeff A = 1)
    (hA : A ^ 2 * (1 - 2 * X * G ^ 2 - 3 * X ^ 2 * G ^ 4) = G ^ 2) (n : ℕ) :
    coeff n A % 4 ≠ 3 := by
  have hG0 : constantCoeff G = 1 := by
    have h := congrArg constantCoeff hG
    simpa using h
  set Gi := invOfUnit G 1 with hGi
  have hGGi : G * Gi = 1 := by
    rw [hGi]
    exact mul_invOfUnit G 1 (by simp [hG0])
  set A₀ := Gi * A
  have hA₀0 : constantCoeff A₀ = 1 := by
    have h := congrArg constantCoeff hGGi
    simp only [map_mul, map_one, hG0, one_mul] at h
    simp [A₀, h, hA0]
  have hA₀ : A₀ ^ 2 * (1 - 2 * X * G ^ 2 - 3 * X ^ 2 * G ^ 4) = 1 := by
    calc A₀ ^ 2 * (1 - 2 * X * G ^ 2 - 3 * X ^ 2 * G ^ 4)
        = Gi ^ 2 * (A ^ 2 * (1 - 2 * X * G ^ 2 - 3 * X ^ 2 * G ^ 4)) := by ring
      _ = (G * Gi) ^ 2 := by rw [hA]; ring
      _ = 1 := by rw [hGGi, one_pow]
  have hGA : G ^ 1 * A₀ = A := by
    calc G ^ 1 * A₀ = (G * Gi) * A := by ring
      _ = A := by rw [hGGi, one_mul]
  have h := OpenProblemsLib.HannaMod4.gf_mod4 G A₀ hG hA₀0 hA₀ 1 le_rfl n
  rwa [hGA] at h
