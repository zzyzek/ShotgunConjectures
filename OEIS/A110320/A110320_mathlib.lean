/-
OEIS A110320 (number of blocks in all RNA secondary structures with n
nodes), conjecture (G. McGarvey 2007): a(n) = (A051292(n+2) - A051286(n+1))/2.

What is checked here: the generating-function algebra.  For any power series
R over ℚ with constant coefficient 1 (the entries use
R = √(1 − 2z − z² − 2z³ + z⁴), but the identity holds for every such R),
define the three sequences by the printed g.f.s
  A051286: 1/R,   A051292: (1 − z² + R)/R,
  A110320: (1 − z − z²)/(2z²R) − 1/(2z²), i.e. a(n) = coefficient of z^(n+2)
           in ((1 − z − z²)/R − 1)/2.
Main theorem `A110320_gf_identity`: a(n) = (A051292(n+2) − A051286(n+1))/2 for
all n.

Not checked here: that the printed g.f.s (Deutsch for A110320, Munarini–Salvi
for A051286 and A051292) generate the combinatorially defined sequences
(checked numerically for n ≤ 40 by certificate/check.py).
-/
import Mathlib

open PowerSeries

variable (R : ℚ⟦X⟧)

noncomputable def a051286 (n : ℕ) : ℚ := coeff n R⁻¹
noncomputable def a051292 (n : ℕ) : ℚ := coeff n ((1 - X ^ 2 + R) * R⁻¹)
noncomputable def a110320 (n : ℕ) : ℚ := coeff (n + 2) ((1 - X - X ^ 2) * R⁻¹ - 1) / 2

theorem A110320_gf_identity (hR : constantCoeff R = 1) (n : ℕ) :
    a110320 R n = (a051292 R (n + 2) - a051286 R (n + 1)) / 2 := by
  have hinv : R * R⁻¹ = 1 := PowerSeries.mul_inv_cancel R (by rw [hR]; norm_num)
  have e1 : (1 - X ^ 2 + R) * R⁻¹ = (1 - X - X ^ 2) * R⁻¹ + X * R⁻¹ + 1 := by
    rw [add_mul, hinv]; ring
  have e2 : coeff (n + 2) (X * R⁻¹) = coeff (n + 1) R⁻¹ := coeff_succ_X_mul (n + 1) _
  have e3 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp
  simp only [a110320, a051292, a051286]
  rw [e1, map_add, map_add, e2, e3, map_sub, e3]
  ring
