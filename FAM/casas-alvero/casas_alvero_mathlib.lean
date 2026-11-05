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


theorem casas_alvero_root_deg_2 [CharZero K] (P : K[X]) (hP : P.Monic)
    (hd : P.natDegree = 2) (h : HasCasasAlveroPropR P) : ∃ a, P = (X - C a) ^ 2 := by
  have hh : ∀ i < 2, ∃ α, P.eval α = 0 ∧ (P.hasseDeriv i).eval α = 0 := fun i hi => by
    obtain ⟨α, h1, h2⟩ := h i (by simp [hd, hi])
    exact ⟨α, h1, h2⟩
  have cd : P.coeff 2 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  obtain ⟨x1, p1, q1⟩ := hh 1 (by norm_num)
  rw [eval_eq_sum_range' (n := 3) (by omega)] at p1
  rw [eval_hasseDeriv_sum P hd] at q1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at p1 q1
  norm_num [Nat.choose, cd] at p1 q1
  set c0 := P.coeff 0 with hc0
  set c1 := P.coeff 1 with hc1
  refine ⟨x1, eq_X_sub_C_pow P hP hd x1 ?_⟩
  intro j hj
  interval_cases j
  · norm_num [Nat.choose]
    linear_combination (1) * p1 + (-x1) * q1
  · norm_num [Nat.choose]
    linear_combination (1) * q1

/-- Casas-Alvero in degree 2, in the formal-conjectures statement shape. -/
theorem casas_alvero_deg_2 [CharZero K] (P : K[X]) (hP : P.Monic) (hd : P.natDegree = 2)
    (hca : HasCasasAlveroProp P) : ∃ α : K, P = (X - C α) ^ P.natDegree :=
  of_algClosure P hP hd hca fun Q hQ hQd hQr => casas_alvero_root_deg_2 Q hQ hQd hQr

theorem core3_r1 {K : Type*} [Field K] (b1 x1 : K)
    (hQ1 : b1*x1 + x1^3 = 0) (hH1 : b1 + 3*x1^2 = 0) :
    (1:K) * (4*b1^3) = 0 := by
  linear_combination (-12*b1*x1 + 18*x1^3) * hQ1 + (4*b1^2 - 6*x1^4) * hH1

theorem core3_t1 {K : Type*} [Field K] (b1 : K)
    (s1 : (4*b1^3) = 0) :
    (4:K) * b1^3 = 0 := by
  linear_combination (1) * s1

theorem core3 {K : Type*} [Field K] [CharZero K] (b1 x1 : K)
    (hQ1 : b1*x1 + x1^3 = 0)
    (hH1 : b1 + 3*x1^2 = 0) :
    b1 = 0 := by
  have s1 := (mul_eq_zero.mp (core3_r1 b1 x1 hQ1 hH1)).resolve_left (by norm_num)
  have z1 : b1 = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
    ((mul_eq_zero.mp (core3_t1 b1 s1)).resolve_left (by norm_num))
  exact z1

theorem casas_alvero_root_deg_3 [CharZero K] (P : K[X]) (hP : P.Monic)
    (hd : P.natDegree = 3) (h : HasCasasAlveroPropR P) : ∃ a, P = (X - C a) ^ 3 := by
  have hh : ∀ i < 3, ∃ α, P.eval α = 0 ∧ (P.hasseDeriv i).eval α = 0 := fun i hi => by
    obtain ⟨α, h1, h2⟩ := h i (by simp [hd, hi])
    exact ⟨α, h1, h2⟩
  have cd : P.coeff 3 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  obtain ⟨x1, p1, q1⟩ := hh 1 (by norm_num)
  obtain ⟨x2, p2, q2⟩ := hh 2 (by norm_num)
  rw [eval_eq_sum_range' (n := 4) (by omega)] at p1 p2
  rw [eval_hasseDeriv_sum P hd] at q1 q2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at p1 p2 q1 q2
  norm_num [Nat.choose, cd] at p1 p2 q1 q2
  set c0 := P.coeff 0 with hc0
  set c1 := P.coeff 1 with hc1
  set c2 := P.coeff 2 with hc2
  obtain z1 := core3 (c1 + 2*c2*x2 + 3*x2^2) (x1 - x2)
    (by linear_combination p1 - p2 - (x1 - x2)^2 * q2)
    (by linear_combination q1 - 2 * (x1 - x2)^1 * q2)
  refine ⟨x2, eq_X_sub_C_pow P hP hd x2 ?_⟩
  intro j hj
  interval_cases j
  · norm_num [Nat.choose]
    linear_combination (1) * p2 + (-x2) * z1 + (x2^2) * q2
  · norm_num [Nat.choose]
    linear_combination (1) * z1 + (-2*x2) * q2
  · norm_num [Nat.choose]
    linear_combination (1) * q2

/-- Casas-Alvero in degree 3, in the formal-conjectures statement shape. -/
theorem casas_alvero_deg_3 [CharZero K] (P : K[X]) (hP : P.Monic) (hd : P.natDegree = 3)
    (hca : HasCasasAlveroProp P) : ∃ α : K, P = (X - C α) ^ P.natDegree :=
  of_algClosure P hP hd hca fun Q hQ hQd hQr => casas_alvero_root_deg_3 Q hQ hQd hQr

theorem core4_r1 {K : Type*} [Field K] (b1 b2 x1 : K)
    (hQ1 : b1*x1 + b2*x1^2 + x1^4 = 0) (hH1 : b1 + 2*b2*x1 + 4*x1^3 = 0) :
    (1:K) * (-27*b1^4 - 4*b1^2*b2^3) = 0 := by
  linear_combination (54*b1^2*b2 + 108*b1^2*x1^2 - 54*b1*b2^2*x1 - 162*b1*b2*x1^3 - 108*b1*x1^5 + 16*b2^4 + 124*b2^3*x1^2 + 340*b2^2*x1^4 + 384*b2*x1^6 + 144*x1^8) * hQ1 + (-27*b1^3 - 4*b1*b2^3 - 8*b2^4*x1 - 54*b2^3*x1^3 - 124*b2^2*x1^5 - 114*b2*x1^7 - 36*x1^9) * hH1

theorem core4_r2 {K : Type*} [Field K] (b1 b2 x2 : K)
    (hQ2 : b1*x2 + b2*x2^2 + x2^4 = 0) (hH2 : b2 + 6*x2^2 = 0) :
    (1:K) * (216*b1^2*b2 + 25*b2^4) = 0 := by
  linear_combination (-1296*b1*x2 + 1296*b2*x2^2 + 1296*x2^4) * hQ2 + (216*b1^2 + 25*b2^3 - 150*b2^2*x2^2 - 396*b2*x2^4 - 216*x2^6) * hH2

theorem core4_t1 {K : Type*} [Field K] (b1 b2 : K)
    (s1 : (-27*b1^4 - 4*b1^2*b2^3) = 0) (s2 : (216*b1^2*b2 + 25*b2^4) = 0) :
    (5103:K) * b1^6 = 0 := by
  linear_combination (-189*b1^2 - 100*b2^3) * s1 + (-16*b1^2*b2^2) * s2

theorem core4_t2 {K : Type*} [Field K] (b1 b2 : K)
    (s1 : (-27*b1^4 - 4*b1^2*b2^3) = 0) (s2 : (216*b1^2*b2 + 25*b2^4) = 0) :
    (175:K) * b2^7 = 0 := by
  linear_combination (1728*b2) * s1 + (216*b1^2 + 7*b2^3) * s2

theorem core4 {K : Type*} [Field K] [CharZero K] (b1 b2 x1 x2 : K)
    (hQ1 : b1*x1 + b2*x1^2 + x1^4 = 0)
    (hH1 : b1 + 2*b2*x1 + 4*x1^3 = 0)
    (hQ2 : b1*x2 + b2*x2^2 + x2^4 = 0)
    (hH2 : b2 + 6*x2^2 = 0) :
    b1 = 0 ∧ b2 = 0 := by
  have s1 := (mul_eq_zero.mp (core4_r1 b1 b2 x1 hQ1 hH1)).resolve_left (by norm_num)
  have s2 := (mul_eq_zero.mp (core4_r2 b1 b2 x2 hQ2 hH2)).resolve_left (by norm_num)
  have z1 : b1 = 0 := pow_eq_zero_iff (n := 6) (by norm_num) |>.mp
    ((mul_eq_zero.mp (core4_t1 b1 b2 s1 s2)).resolve_left (by norm_num))
  have z2 : b2 = 0 := pow_eq_zero_iff (n := 7) (by norm_num) |>.mp
    ((mul_eq_zero.mp (core4_t2 b1 b2 s1 s2)).resolve_left (by norm_num))
  exact ⟨z1, z2⟩

theorem casas_alvero_root_deg_4 [CharZero K] (P : K[X]) (hP : P.Monic)
    (hd : P.natDegree = 4) (h : HasCasasAlveroPropR P) : ∃ a, P = (X - C a) ^ 4 := by
  have hh : ∀ i < 4, ∃ α, P.eval α = 0 ∧ (P.hasseDeriv i).eval α = 0 := fun i hi => by
    obtain ⟨α, h1, h2⟩ := h i (by simp [hd, hi])
    exact ⟨α, h1, h2⟩
  have cd : P.coeff 4 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  obtain ⟨x1, p1, q1⟩ := hh 1 (by norm_num)
  obtain ⟨x2, p2, q2⟩ := hh 2 (by norm_num)
  obtain ⟨x3, p3, q3⟩ := hh 3 (by norm_num)
  rw [eval_eq_sum_range' (n := 5) (by omega)] at p1 p2 p3
  rw [eval_hasseDeriv_sum P hd] at q1 q2 q3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at p1 p2 p3 q1 q2 q3
  norm_num [Nat.choose, cd] at p1 p2 p3 q1 q2 q3
  set c0 := P.coeff 0 with hc0
  set c1 := P.coeff 1 with hc1
  set c2 := P.coeff 2 with hc2
  set c3 := P.coeff 3 with hc3
  obtain ⟨z1, z2⟩ := core4 (c1 + 2*c2*x3 + 3*c3*x3^2 + 4*x3^3) (c2 + 3*c3*x3 + 6*x3^2) (x1 - x3) (x2 - x3)
    (by linear_combination p1 - p3 - (x1 - x3)^3 * q3)
    (by linear_combination q1 - 3 * (x1 - x3)^2 * q3)
    (by linear_combination p2 - p3 - (x2 - x3)^3 * q3)
    (by linear_combination q2 - 3 * (x2 - x3)^1 * q3)
  refine ⟨x3, eq_X_sub_C_pow P hP hd x3 ?_⟩
  intro j hj
  interval_cases j
  · norm_num [Nat.choose]
    linear_combination (1) * p3 + (-x3) * z1 + (x3^2) * z2 + (-x3^3) * q3
  · norm_num [Nat.choose]
    linear_combination (1) * z1 + (-2*x3) * z2 + (3*x3^2) * q3
  · norm_num [Nat.choose]
    linear_combination (1) * z2 + (-3*x3) * q3
  · norm_num [Nat.choose]
    linear_combination (1) * q3

/-- Casas-Alvero in degree 4, in the formal-conjectures statement shape. -/
theorem casas_alvero_deg_4 [CharZero K] (P : K[X]) (hP : P.Monic) (hd : P.natDegree = 4)
    (hca : HasCasasAlveroProp P) : ∃ α : K, P = (X - C α) ^ P.natDegree :=
  of_algClosure P hP hd hca fun Q hQ hQd hQr => casas_alvero_root_deg_4 Q hQ hQd hQr

theorem core5_r1 {K : Type*} [Field K] (b1 b2 b3 x1 : K)
    (hQ1 : b1*x1 + b2*x1^2 + b3*x1^3 + x1^5 = 0) (hH1 : b1 + 2*b2*x1 + 3*b3*x1^2 + 5*x1^4 = 0) :
    (1:K) * (256*b1^5 - 128*b1^4*b3^2 + 144*b1^3*b2^2*b3 + 16*b1^3*b3^4 - 27*b1^2*b2^4 - 4*b1^2*b2^2*b3^3) = 0 := by
  linear_combination (-512*b1^3*b2 - 768*b1^3*b3*x1 - 1280*b1^3*x1^3 + 512*b1^2*b2^2*x1 + 256*b1^2*b2*b3^2 + 1280*b1^2*b2*b3*x1^2 + 1792*b1^2*b2*x1^4 + 384*b1^2*b3^3*x1 + 1408*b1^2*b3^2*x1^3 + 2048*b1^2*b3*x1^5 + 1280*b1^2*x1^7 - 288*b1*b2^3*b3 - 512*b1*b2^3*x1^2 - 688*b1*b2^2*b3^2*x1 - 2512*b1*b2^2*b3*x1^3 - 2304*b1*b2^2*x1^5 - 32*b1*b2*b3^4 - 640*b1*b2*b3^3*x1^2 - 2944*b1*b2*b3^2*x1^4 - 5120*b1*b2*b3*x1^6 - 3072*b1*b2*x1^8 - 48*b1*b3^5*x1 - 464*b1*b3^4*x1^3 - 1792*b1*b3^3*x1^5 - 3456*b1*b3^2*x1^7 - 3328*b1*b3*x1^9 - 1280*b1*x1^11 + 108*b2^5 + 684*b2^4*b3*x1 + 1132*b2^4*x1^3 + 16*b2^3*b3^3 + 1691*b2^3*b3^2*x1^2 + 5410*b2^3*b3*x1^4 + 4339*b2^3*x1^6 + 80*b2^2*b3^4*x1 + 2218*b2^2*b3^3*x1^3 + 9520*b2^2*b3^2*x1^5 + 14562*b2^2*b3*x1^7 + 7476*b2^2*x1^9 + 132*b2*b3^5*x1^2 + 1780*b2*b3^4*x1^4 + 8012*b2*b3^3*x1^6 + 16364*b2*b3^2*x1^8 + 15648*b2*b3*x1^10 + 5680*b2*x1^12 + 72*b3^6*x1^3 + 744*b3^5*x1^5 + 3176*b3^4*x1^7 + 7160*b3^3*x1^9 + 8976*b3^2*x1^11 + 5920*b3*x1^13 + 1600*x1^15) * hQ1 + (256*b1^4 - 128*b1^3*b3^2 + 144*b1^2*b2^2*b3 + 16*b1^2*b3^4 - 27*b1*b2^4 - 4*b1*b2^2*b3^3 - 54*b2^5*x1 - 315*b2^4*b3*x1^2 - 485*b2^4*x1^4 - 8*b2^3*b3^3*x1 - 715*b2^3*b3^2*x1^3 - 2098*b2^3*b3*x1^5 - 1523*b2^3*x1^7 - 36*b2^2*b3^4*x1^2 - 870*b2^2*b3^3*x1^4 - 3376*b2^2*b3^2*x1^6 - 4626*b2^2*b3*x1^8 - 2100*b2^2*x1^10 - 52*b2*b3^5*x1^3 - 644*b2*b3^4*x1^5 - 2636*b2*b3^3*x1^7 - 4844*b2*b3^2*x1^9 - 4128*b2*b3*x1^11 - 1328*b2*x1^13 - 24*b3^6*x1^4 - 232*b3^5*x1^6 - 920*b3^4*x1^8 - 1912*b3^3*x1^10 - 2192*b3^2*x1^12 - 1312*b3*x1^14 - 320*x1^16) * hH1

theorem core5_r2 {K : Type*} [Field K] (b1 b2 b3 x2 : K)
    (hQ2 : b1*x2 + b2*x2^2 + b3*x2^3 + x2^5 = 0) (hH2 : b2 + 3*b3*x2 + 10*x2^3 = 0) :
    (1:K) * (10000*b1^3*b2 - 4200*b1^2*b2*b3^2 + 4320*b1*b2^3*b3 + 441*b1*b2*b3^4 - 729*b2^5 - 98*b2^3*b3^3) = 0 := by
  linear_combination (-30000*b1^2*b3 - 100000*b1^2*x2^2 + 30000*b1*b2*b3*x2 + 100000*b1*b2*x2^3 + 12600*b1*b3^3 + 72000*b1*b3^2*x2^2 + 130000*b1*b3*x2^4 + 100000*b1*x2^6 - 12960*b2^2*b3^2 - 73200*b2^2*b3*x2^2 - 100000*b2^2*x2^4 - 12600*b2*b3^3*x2 - 102000*b2*b3^2*x2^3 - 260000*b2*b3*x2^5 - 200000*b2*x2^7 - 1323*b3^5 - 17010*b3^4*x2^2 - 84600*b3^3*x2^4 - 202000*b3^2*x2^6 - 230000*b3*x2^8 - 100000*x2^10) * hQ2 + (10000*b1^3 - 4200*b1^2*b3^2 + 4320*b1*b2^2*b3 + 441*b1*b3^4 - 729*b2^4 + 2187*b2^3*b3*x2 + 7290*b2^3*x2^3 - 98*b2^2*b3^3 + 6399*b2^2*b3^2*x2^2 + 29460*b2^2*b3*x2^4 + 27100*b2^2*x2^6 + 294*b2*b3^4*x2 + 7343*b2*b3^3*x2^3 + 35790*b2*b3^2*x2^5 + 57300*b2*b3*x2^7 + 29000*b2*x2^9 + 441*b3^5*x2^2 + 4641*b3^4*x2^4 + 18400*b3^3*x2^6 + 34200*b3^2*x2^8 + 30000*b3*x2^10 + 10000*x2^12) * hH2

theorem core5_r3 {K : Type*} [Field K] (b1 b2 b3 x3 : K)
    (hQ3 : b1*x3 + b2*x3^2 + b3*x3^3 + x3^5 = 0) (hH3 : b3 + 10*x3^2 = 0) :
    (1:K) * (10000*b1^2*b3 - 1800*b1*b3^3 + 1000*b2^2*b3^2 + 81*b3^5) = 0 := by
  linear_combination (-100000*b1*x3 + 100000*b2*x3^2 + 18000*b3^2*x3 + 100000*b3*x3^3 + 100000*x3^5) * hQ3 + (10000*b1^2 - 1800*b1*b3^2 + 1000*b2^2*b3 - 10000*b2^2*x3^2 - 18000*b2*b3*x3^3 - 20000*b2*x3^5 + 81*b3^4 - 810*b3^3*x3^2 - 9900*b3^2*x3^4 - 19000*b3*x3^6 - 10000*x3^8) * hH3

theorem core5_t1 {K : Type*} [Field K] (b1 b2 b3 : K)
    (s1 : (256*b1^5 - 128*b1^4*b3^2 + 144*b1^3*b2^2*b3 + 16*b1^3*b3^4 - 27*b1^2*b2^4 - 4*b1^2*b2^2*b3^3) = 0) (s2 : (10000*b1^3*b2 - 4200*b1^2*b2*b3^2 + 4320*b1*b2^3*b3 + 441*b1*b2*b3^4 - 729*b2^5 - 98*b2^3*b3^3) = 0) (s3 : (10000*b1^2*b3 - 1800*b1*b3^3 + 1000*b2^2*b3^2 + 81*b3^5) = 0) :
    (164790817540136787344840463692595200000000:K) * b1^10 = 0 := by
  linear_combination (643714131016159325565783061299200000000*b1^5 + 321857065508079662782891530649600000000*b1^4*b3^2 - 362089198696589620630752971980800000000*b1^3*b2^2*b3 + 120696399565529873543584323993600000000*b1^3*b3^4 - 151964896862299270834668345753600000000*b1^2*b2^4 + 9258520356567384412739921653008250000000*b1^2*b2^2*b3^3 + 40232133188509957847861441331200000000*b1^2*b3^6 + 1993618451213176849622270048426850000000*b1*b2^4*b3^2 - 2722264409081180148832925740489575000000*b1*b2^2*b3^5 - 11215836690583449247443062334000000000*b1*b3^8 + 1793443667617534520589978559483518750000*b2^6*b3 + 2587418281995361257988635498698287500000*b2^4*b3^4 + 253287068425982626657368819110703125000*b2^2*b3^7 + 571841919938614284290816232300000000*b3^10) * s1 + (5628329513418491512395123916800000000*b1^4*b2^3 - 246030118962351271524062957175200000000*b1^4*b2*b3^3 - 44534786097156285955211266091040000000*b1^3*b2^3*b3^2 + 83836436862727343332182201203376000000*b1^3*b2*b3^5 - 47132942562469354536141953500332000000*b1^2*b2^5*b3 - 86285904644406592707638197334216400000*b1^2*b2^3*b3^4 - 10612598387955232377738036001041360000*b1^2*b2*b3^7 + 747945926632193585243887106365635000*b1*b2^5*b3^3 + 37275106309034430316473575771124000*b1*b2^3*b3^6 + 267380818397874668237438544129475200*b1*b2*b3^9 + 1929089697892081289311651166572425000*b2^7*b3^2 + 571954990983721591559760430237006425*b2^5*b3^5 - 94907346212845105681834111211516160*b2^3*b3^8 - 10414894380947185349979077983303392*b2*b3^11) * s2 + (608982484787015963517433926400000000*b1^4*b3^7 - 112956428629849735168556292800000000*b1^3*b3^9 - 707458823461778192539065386733328000*b1^2*b2^2*b3^8 - 5257063412804932978348790678275992000*b1*b2^8*b3 - 1909508437824134984439062744163477825*b1*b2^6*b3^4 + 415619311308583447510620282108268800*b1*b2^4*b3^7 + 56703313851823564683219424575762912*b1*b2^2*b3^10 + 1406306389763327259908193700431297825*b2^10 + 492095161249727498547043478231940210*b2^8*b3^3 - 52995574333987293451511066646755808*b2^6*b3^6 - 12600736411516347707382094350169536*b2^4*b3^9) * s3

theorem core5_t2 {K : Type*} [Field K] (b1 b2 b3 : K)
    (s1 : (256*b1^5 - 128*b1^4*b3^2 + 144*b1^3*b2^2*b3 + 16*b1^3*b3^4 - 27*b1^2*b2^4 - 4*b1^2*b2^2*b3^3) = 0) (s2 : (10000*b1^3*b2 - 4200*b1^2*b2*b3^2 + 4320*b1*b2^3*b3 + 441*b1*b2*b3^4 - 729*b2^5 - 98*b2^3*b3^3) = 0) (s3 : (10000*b1^2*b3 - 1800*b1*b3^3 + 1000*b2^2*b3^2 + 81*b3^5) = 0) :
    (895599815831446969090505499940703515542699375:K) * b2^13 = 0 := by
  linear_combination (-14635872111318047805185325097307492812500000000*b1^2*b2^3*b3 - 568407193404479309310685798898382502692957031250000*b1^2*b2*b3^4 - 1473483956183893877759287656145080082031250000*b1*b2^5 - 226531677731789272256593497416274595076820312500000*b1*b2^3*b3^3 + 200564381998454647789295484623417438164001953125000*b1*b2*b3^6 - 155716288216885356809004249245630101116623671875000*b2^5*b3^2 - 210936013976463041410040774514784739091110812500000*b2^3*b3^5 - 20561733551479277770393698239491696901921005078125*b2*b3^8) * s1 + (374678326049742023812744322491071816000000000*b1^4*b2^2*b3 + 14551224151154670318353556451798592068939700000000*b1^4*b3^4 + 37721189278307683270637763997314050100000000*b1^3*b2^4 + 5799180975667721390406888514310830348221320000000*b1^3*b2^2*b3^3 - 6298546111252812608874248922503373782513626000000*b1^3*b3^6 + 3986382856178672361029954692801095888333546000000*b1^2*b2^4*b3^2 + 6834954138417877950981917508115973350720136450000*b1^2*b2^2*b3^5 + 715957626153153640755581769372407754601170290000*b1^2*b3^8 - 7280189530713382871233088451481611669300000*b1*b2^6*b3 - 35994381736065483500296815945865917878177634375*b1*b2^4*b3^4 + 25490501183690295920900341616915446385275751500*b1*b2^2*b3^7 + 14746731589748732673245251122756097240493260800*b1*b3^10 - 1228531983307883359520583676187521969194375*b2^8 - 178084936235372572321356884487975411634021061250*b2^6*b3^3 - 75576958654518131190980352325531216764497285800*b2^4*b3^6 - 15652590584519827997810340990915026863961973760*b2^2*b3^9 - 866640915155815177713572434359985173689278464*b3^12) * s2 + (-20371845755637359428458643366907677906142822400*b1^2*b2*b3^9 + 509403578534150658910876406642168662999986510000*b1*b2^7*b3^2 + 267163431333777739941755446482014553447050678400*b1*b2^5*b3^5 + 67730015492025723538359646274394869721721226240*b1*b2^3*b3^8 + 4718378315848327078662783253737697056752738304*b1*b2*b3^11 - 129824038911720969394838401808934341458354334700*b2^9*b3 - 62032179458360831204735740978610165703325884240*b2^7*b3^4 - 13792673948130504139536218091011690404779616256*b2^5*b3^7 - 1048528514632961573036174056386154901500608512*b2^3*b3^10) * s3

theorem core5_t3 {K : Type*} [Field K] (b1 b2 b3 : K)
    (s1 : (256*b1^5 - 128*b1^4*b3^2 + 144*b1^3*b2^2*b3 + 16*b1^3*b3^4 - 27*b1^2*b2^4 - 4*b1^2*b2^2*b3^3) = 0) (s2 : (10000*b1^3*b2 - 4200*b1^2*b2*b3^2 + 4320*b1*b2^3*b3 + 441*b1*b2*b3^4 - 729*b2^5 - 98*b2^3*b3^3) = 0) (s3 : (10000*b1^2*b3 - 1800*b1*b3^3 + 1000*b2^2*b3^2 + 81*b3^5) = 0) :
    (658410697702446765961561551538126848:K) * b3^19 = 0 := by
  linear_combination (25200379435877581488585431654931640625000000000*b1^2*b2^2*b3^2 + 4685260565423209581240425600657958984375000000*b1*b2^4*b3 - 5103597311875495215469093427242109375000000000*b1*b2^2*b3^4 - 2871099094860279090061377657187500000000*b1*b3^7 + 3442679714613448456590266106076076660156250000*b2^4*b3^3 + 304605961962934795858988104519798242187500000*b2^2*b3^6 + 396211675090718514428470116691875000000*b3^9) * s1 + (-645129713558466086107787050366250000000000000*b1^4*b2*b3^2 - 119942670474834165279754895376843750000000000*b1^3*b2^3*b3 + 182262468268689964404631755766698000000000000*b1^3*b2*b3^4 - 162726614675497371503396630758195687500000000*b1^2*b2^3*b3^3 - 8444108274883460466432435649131675000000000*b1^2*b2*b3^6 + 5358549861491433772914975649937695312500000*b1*b2^5*b3^2 + 15720936513495537010849082428496111054687500*b1*b2^3*b3^5 - 1299280274248673761549136629337293650000000*b1*b2*b3^8 - 5732893837759727023348782265919504296875000*b2^5*b3^4 + 481029726042700287288191808051616651953125*b2^3*b3^7 + 76574347909027341458825193083710816500000*b2*b3^10) * s2 + (73500136828423144705571268024000000000*b1^4*b3^6 - 33663062667417800275151640754992000000*b1^3*b3^8 - 43694463886478110007535864834642198304687500*b1^2*b2^4*b3^4 + 1779725954088033812853276775542861950000000*b1^2*b2^2*b3^7 + 3010565604492212007140199138263040000*b1^2*b3^10 + 3906382849027255220455017248804579882812500*b1*b2^8 + 28912681679206906258626259606347073153125000*b1*b2^6*b3^3 - 1069029291333916687979073046367227385078125*b1*b2^4*b3^6 - 416909243157451810478799592269297057300000*b1*b2^2*b3^9 + 180633936269532720428411948295782400*b1*b3^12 - 4179279607726841000021262271855318632421875*b2^8*b3^2 + 127368722410549382146633410029797927406250*b2^6*b3^5 + 92646746262611060123849056734669985000000*b2^4*b3^8 - 100352186816407066904673304608768000*b2^2*b3^11 + 8128527132128972419278537673310208*b3^14) * s3

theorem core5 {K : Type*} [Field K] [CharZero K] (b1 b2 b3 x1 x2 x3 : K)
    (hQ1 : b1*x1 + b2*x1^2 + b3*x1^3 + x1^5 = 0)
    (hH1 : b1 + 2*b2*x1 + 3*b3*x1^2 + 5*x1^4 = 0)
    (hQ2 : b1*x2 + b2*x2^2 + b3*x2^3 + x2^5 = 0)
    (hH2 : b2 + 3*b3*x2 + 10*x2^3 = 0)
    (hQ3 : b1*x3 + b2*x3^2 + b3*x3^3 + x3^5 = 0)
    (hH3 : b3 + 10*x3^2 = 0) :
    b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  have s1 := (mul_eq_zero.mp (core5_r1 b1 b2 b3 x1 hQ1 hH1)).resolve_left (by norm_num)
  have s2 := (mul_eq_zero.mp (core5_r2 b1 b2 b3 x2 hQ2 hH2)).resolve_left (by norm_num)
  have s3 := (mul_eq_zero.mp (core5_r3 b1 b2 b3 x3 hQ3 hH3)).resolve_left (by norm_num)
  have z1 : b1 = 0 := pow_eq_zero_iff (n := 10) (by norm_num) |>.mp
    ((mul_eq_zero.mp (core5_t1 b1 b2 b3 s1 s2 s3)).resolve_left (by norm_num))
  have z2 : b2 = 0 := pow_eq_zero_iff (n := 13) (by norm_num) |>.mp
    ((mul_eq_zero.mp (core5_t2 b1 b2 b3 s1 s2 s3)).resolve_left (by norm_num))
  have z3 : b3 = 0 := pow_eq_zero_iff (n := 19) (by norm_num) |>.mp
    ((mul_eq_zero.mp (core5_t3 b1 b2 b3 s1 s2 s3)).resolve_left (by norm_num))
  exact ⟨z1, z2, z3⟩

theorem casas_alvero_root_deg_5 [CharZero K] (P : K[X]) (hP : P.Monic)
    (hd : P.natDegree = 5) (h : HasCasasAlveroPropR P) : ∃ a, P = (X - C a) ^ 5 := by
  have hh : ∀ i < 5, ∃ α, P.eval α = 0 ∧ (P.hasseDeriv i).eval α = 0 := fun i hi => by
    obtain ⟨α, h1, h2⟩ := h i (by simp [hd, hi])
    exact ⟨α, h1, h2⟩
  have cd : P.coeff 5 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  obtain ⟨x1, p1, q1⟩ := hh 1 (by norm_num)
  obtain ⟨x2, p2, q2⟩ := hh 2 (by norm_num)
  obtain ⟨x3, p3, q3⟩ := hh 3 (by norm_num)
  obtain ⟨x4, p4, q4⟩ := hh 4 (by norm_num)
  rw [eval_eq_sum_range' (n := 6) (by omega)] at p1 p2 p3 p4
  rw [eval_hasseDeriv_sum P hd] at q1 q2 q3 q4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at p1 p2 p3 p4 q1 q2 q3 q4
  norm_num [Nat.choose, cd] at p1 p2 p3 p4 q1 q2 q3 q4
  set c0 := P.coeff 0 with hc0
  set c1 := P.coeff 1 with hc1
  set c2 := P.coeff 2 with hc2
  set c3 := P.coeff 3 with hc3
  set c4 := P.coeff 4 with hc4
  obtain ⟨z1, z2, z3⟩ := core5 (c1 + 2*c2*x4 + 3*c3*x4^2 + 4*c4*x4^3 + 5*x4^4) (c2 + 3*c3*x4 + 6*c4*x4^2 + 10*x4^3) (c3 + 4*c4*x4 + 10*x4^2) (x1 - x4) (x2 - x4) (x3 - x4)
    (by linear_combination p1 - p4 - (x1 - x4)^4 * q4)
    (by linear_combination q1 - 4 * (x1 - x4)^3 * q4)
    (by linear_combination p2 - p4 - (x2 - x4)^4 * q4)
    (by linear_combination q2 - 6 * (x2 - x4)^2 * q4)
    (by linear_combination p3 - p4 - (x3 - x4)^4 * q4)
    (by linear_combination q3 - 4 * (x3 - x4)^1 * q4)
  refine ⟨x4, eq_X_sub_C_pow P hP hd x4 ?_⟩
  intro j hj
  interval_cases j
  · norm_num [Nat.choose]
    linear_combination (1) * p4 + (-x4) * z1 + (x4^2) * z2 + (-x4^3) * z3 + (x4^4) * q4
  · norm_num [Nat.choose]
    linear_combination (1) * z1 + (-2*x4) * z2 + (3*x4^2) * z3 + (-4*x4^3) * q4
  · norm_num [Nat.choose]
    linear_combination (1) * z2 + (-3*x4) * z3 + (6*x4^2) * q4
  · norm_num [Nat.choose]
    linear_combination (1) * z3 + (-4*x4) * q4
  · norm_num [Nat.choose]
    linear_combination (1) * q4

/-- Casas-Alvero in degree 5, in the formal-conjectures statement shape. -/
theorem casas_alvero_deg_5 [CharZero K] (P : K[X]) (hP : P.Monic) (hd : P.natDegree = 5)
    (hca : HasCasasAlveroProp P) : ∃ α : K, P = (X - C α) ^ P.natDegree :=
  of_algClosure P hP hd hca fun Q hQ hQd hQr => casas_alvero_root_deg_5 Q hQ hQd hQr

