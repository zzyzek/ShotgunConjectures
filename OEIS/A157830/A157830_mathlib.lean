/-
OEIS A157830 (expansion of 1/p(x), p(x) = 1 + 759x^8 + 2576x^12 + 759x^16 + x^24, the weight
enumerator of the binary Golay code C_24). Old comment (Bagula/Adamson 2009): "Conjecture:
An higher symmetry elliptical Invariant than E8 exists ... s[1/x]=s[x] which checks in
Mathematica", with s = p^3 / (q1^3 q2^3), q1 = 24 + 440x^3 + 264x^6 + x^12,
q2 = 1 + 264x^6 + 440x^9 + 24x^12. The first sentence is not a mathematical statement;
the checkable part is the identity s(1/x) = s(x).

  * `A157830_main`: s(x⁻¹) = s(x) for every nonzero x in any field. Reason: p is
    palindromic of degree 24 and q2 is the reversal of q1 (degree 12), so numerator and
    denominator both pick up the factor x^(-72).
Checked: the identity. Not checked: nothing (the "higher invariant" sentence has no content
to check).
-/
import Mathlib

def A157830_pp {K : Type*} [Field K] (x : K) : K := 1 + 759 * x ^ 8 + 2576 * x ^ 12 + 759 * x ^ 16 + x ^ 24
def A157830_q1 {K : Type*} [Field K] (x : K) : K := 24 + 440 * x ^ 3 + 264 * x ^ 6 + x ^ 12
def A157830_q2 {K : Type*} [Field K] (x : K) : K := 1 + 264 * x ^ 6 + 440 * x ^ 9 + 24 * x ^ 12

def A157830_s {K : Type*} [Field K] (x : K) : K :=
  A157830_pp x ^ 3 / (A157830_q1 x ^ 3 * A157830_q2 x ^ 3)

theorem A157830_main {K : Type*} [Field K] (x : K) (hx : x ≠ 0) :
    A157830_s x⁻¹ = A157830_s x := by
  have hp : A157830_pp x⁻¹ = (x ^ 24)⁻¹ * A157830_pp x := by
    unfold A157830_pp; field_simp; ring
  have hq : A157830_q1 x⁻¹ * A157830_q2 x⁻¹ = (x ^ 24)⁻¹ * (A157830_q1 x * A157830_q2 x) := by
    unfold A157830_q1 A157830_q2; field_simp; ring
  have hc : ((x ^ 24)⁻¹) ^ 3 ≠ 0 := by positivity
  unfold A157830_s
  rw [← mul_pow, hp, hq, ← mul_pow, mul_pow, mul_pow, mul_div_mul_left _ _ hc, mul_pow]
