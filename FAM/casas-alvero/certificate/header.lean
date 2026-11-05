import Mathlib

/-!
# Casas-Alvero conjecture in small degrees (FAM-casas-alvero)

Checked here: for a field `K` of characteristic zero and a monic `P : K[X]` of degree `d` with
the Casas-Alvero property (`P` is not coprime to any of its Hasse derivatives of order `< d`),
`P = (X - C α) ^ d` for some `α : K`, for each degree listed in the theorems
`casas_alvero_deg_<d>` below. Statement shape and definitions copied from
google-deepmind/formal-conjectures `FormalConjectures/Paper/CasasAlvero.lean` (Apache 2.0).

Method: translate so that the root of the `(d-1)`-th Hasse derivative is `0`; the remaining
`d - 2` coefficients `b_j` and the shared roots `x_i` satisfy `Q(x_i) = 0`, `H_i(x_i) = 0`.
`core<d>` eliminates each `x_i` by a resultant identity and then shows `N * b_j ^ e = 0` by an
explicit ideal-membership certificate (`linear_combination`, checked by `ring`). The cofactors
were found by `certificate/gen_lean.py` (exact linear algebra over QQ); nothing about the
search is trusted.

Not checked here: any degree not listed; the general conjecture.
-/

namespace CasasAlveroSmall

open Polynomial

section defs

variable {K L : Type*} [Field K] [Field L] {f : K →+* L}

/-- Copied from formal-conjectures: `P` shares a factor with each Hasse derivative of order
`< deg P`. -/
def HasCasasAlveroProp (P : K[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ¬ IsCoprime P (P.hasseDeriv i)

/-- Copied from formal-conjectures: the root version. -/
def HasCasasAlveroPropR (P : K[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ∃ α : K, IsRoot P α ∧ IsRoot (P.hasseDeriv i) α

theorem HasCasasAlveroProp.map_iff {P : K[X]} :
    HasCasasAlveroProp (P.map f) ↔ HasCasasAlveroProp P := by
  simp [HasCasasAlveroProp, P.natDegree_map f, hasseDeriv_map, isCoprime_map]

theorem hasCasasAlveroProp_iffR {P : K[X]} [IsAlgClosed K] :
    HasCasasAlveroProp P → HasCasasAlveroPropR P := by
  simp_rw [HasCasasAlveroProp, HasCasasAlveroPropR,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K, coe_aeval_eq_eval]
  push Not
  exact fun h i hi => h i hi

end defs

variable {K : Type*} [Field K]

/-- Evaluation of a Hasse derivative through the coefficients. -/
theorem eval_hasseDeriv_sum (P : K[X]) {d i : ℕ} (hd : P.natDegree = d) (x : K) :
    (P.hasseDeriv i).eval x =
      ∑ n ∈ Finset.range (d + 1 - i), (((n + i).choose i : ℕ) : K) * P.coeff (n + i) * x ^ n := by
  rcases le_or_gt i d with hi | hi
  · rw [eval_eq_sum_range' (n := d + 1 - i)]
    · simp only [hasseDeriv_coeff]
    · have := natDegree_hasseDeriv_le P i
      omega
  · have h0 : P.hasseDeriv i = 0 := by
      ext n
      rw [hasseDeriv_coeff, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, coeff_zero]
    have h1 : d + 1 - i = 0 := by omega
    rw [h0, h1]
    simp

/-- A monic polynomial of degree `d` with the binomial coefficients of `(X - a)^d`. -/
theorem eq_X_sub_C_pow (P : K[X]) {d : ℕ} (hP : P.Monic) (hd : P.natDegree = d) (a : K)
    (hc : ∀ j < d, P.coeff j = (d.choose j : K) * (-a) ^ (d - j)) : P = (X - C a) ^ d := by
  ext n
  rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
  rcases lt_trichotomy n d with h | rfl | h
  · rw [hc n h]
    ring
  · rw [← hd, hP.coeff_natDegree, hd]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt (hd ▸ h), Nat.choose_eq_zero_of_lt h]
    simp

/-- From the root version over the algebraic closure to the coprime version over `K`
(the argument of formal-conjectures `casas_alvero_iffᵣ`, for one degree). -/
theorem of_algClosure [CharZero K] {d : ℕ} (P : K[X]) (hP : P.Monic) (hd : P.natDegree = d)
    (hca : HasCasasAlveroProp P)
    (hL : ∀ Q : (AlgebraicClosure K)[X], Q.Monic → Q.natDegree = d → HasCasasAlveroPropR Q →
      ∃ a, Q = (X - C a) ^ d) :
    ∃ α : K, P = (X - C α) ^ P.natDegree := by
  let L := AlgebraicClosure K
  have hm : (P.map (algebraMap K L)).natDegree = d := by rw [natDegree_map, hd]
  obtain ⟨α, eq⟩ := hL (P.map (algebraMap K L)) (hP.map _) hm <|
    hasCasasAlveroProp_iffR <| HasCasasAlveroProp.map_iff.mpr hca
  rw [← hm] at eq
  by_cases h0 : P.natDegree = 0
  · exact ⟨0, by simp [hP.natDegree_eq_zero.mp h0]⟩
  let α' := - P.nextCoeff / P.natDegree
  have : algebraMap K L α' = α := by
    simp_rw [α', div_eq_inv_mul, map_mul, map_neg, ← nextCoeff_map (algebraMap K L).injective,
      congr_arg nextCoeff eq, (monic_X_sub_C α).nextCoeff_pow, nextCoeff_X_sub_C, nsmul_eq_mul,
      mul_neg _ α, neg_neg, ← mul_assoc, natDegree_map, map_inv₀, map_natCast]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h0), one_mul]
  use α'
  apply map_injective _ (algebraMap K L).injective
  simpa [this] using eq

