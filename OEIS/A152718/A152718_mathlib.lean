/-
OEIS A152718: the inverse Motzkin transform of A054393 (conjecture of R. J. Mathar, 2008).

Checked here (Mathlib):
* `A054393 n` is the number of walks of length n on the levels 0, 1, 2, ... that start and end at
  level 0, where a step goes up by one level, drops to any lower level, or (only at levels 0..4)
  stays put. `w n j` counts such walks ending at level j (dynamic programming over the length).
* `A152718 n` is defined by the recurrence of its OEIS name with the initial terms 1,1,1,1,2,4.
* `zM` is the power series with coefficients `mot`, the unique series with `zM = X * (1 + zM + zM^2)`
  (so `zM = x * M(x)` for the Motzkin series M, `zM_eq`).
* Main results: `A152718_motzkin` (series form: the g.f. of A054393 equals the g.f. of A152718 with
  `zM` substituted) and `A152718_motzkin_coeff` (a054393(n) = sum_{k<=n} a152718(k) [x^n] zM^k).
Not checked here: that `w`/`A054393` is the OEIS definition (the Mathematica matrix power of the
entry, Alcover); certificate/check.py compares both and the OEIS data terms.
-/
import Mathlib

open PowerSeries Finset

namespace OEIS152718

/-- Walk counts: `w n j` = walks of length n from level 0 to level j. -/
def w : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j => (if j = 0 then 0 else w n (j - 1)) + (if j ≤ 4 then w n j else 0) +
      ∑ i ∈ Ioc j n, w n i

/-- A054393 via the walk model. -/
def A054393 (n : ℕ) : ℕ := w n 0

/-- A152718 by its defining recurrence. -/
def A152718 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 4
  | n + 6 => 2 * A152718 (n + 5) - A152718 (n + 4) + 2 * A152718 (n + 3) - A152718 (n + 2) +
      A152718 (n + 1)

/-- Coefficients of z = x M(x): mot (n+1) = [n=0] + mot n + sum mot i * mot (n-i). -/
def mot : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if n = 0 then 1 else 0) + mot n + ∑ i : Fin (n + 1), mot i * mot (n - i)
decreasing_by all_goals first | (simp_wf; done) | (simp_wf; omega)

noncomputable def zM : ℚ⟦X⟧ := mk fun n => (mot n : ℚ)

lemma zM_eq : zM = X * (1 + zM + zM ^ 2) := by
  ext n
  rcases n with _ | n
  · simp [zM, mot]
  · rw [coeff_succ_X_mul]
    simp only [map_add, coeff_one, zM, coeff_mk, pow_two, coeff_mul]
    rw [mot]
    push_cast
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (mot i : ℚ) * mot j),
      ← Fin.sum_univ_eq_sum_range (fun i => (mot i : ℚ) * mot (n - i))]

lemma constantCoeff_zM : constantCoeff zM = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [zM, mot]

section Alg
variable {A : Type*} [CommRing A]

def uu (z : A) : A := 1 + z + z ^ 2
def QQ (z : A) : A := 1 - 2 * z + z ^ 2 - 2 * z ^ 3 + z ^ 4 - z ^ 5
def PP (z : A) : A := 1 - z - 2 * z ^ 3 - z ^ 5

def Ug (z p q : A) : ℕ → A
  | 0 => uu z * (1 - 2 * z + z ^ 2 - z ^ 3) * q
  | 1 => uu z * (1 - z - z ^ 3) * q
  | 2 => uu z ^ 2 * (1 - z) * q
  | 3 => uu z ^ 2 * q
  | k + 4 => uu z ^ 3 * q * (uu z * p) ^ k

def Rt (z p q : A) (k : ℕ) : A := uu z ^ 3 * q * (uu z * p) ^ (k + 1) * (1 + z)

def Rg (x z p q : A) : ℕ → A
  | 0 => Ug z p q 1 + x * (Ug z p q 2 + x * (Ug z p q 3 + x * (Ug z p q 4 + x * Rt z p q 0)))
  | 1 => Ug z p q 2 + x * (Ug z p q 3 + x * (Ug z p q 4 + x * Rt z p q 0))
  | 2 => Ug z p q 3 + x * (Ug z p q 4 + x * Rt z p q 0)
  | 3 => Ug z p q 4 + x * Rt z p q 0
  | k + 4 => Rt z p q k

variable (x z v p q : A) (hx : x = z * v) (hv : (1 + z + z ^ 2) * v = 1) (hp : (1 + z) * p = 1)
  (hq : (1 - 2 * z + z ^ 2 - 2 * z ^ 3 + z ^ 4 - z ^ 5) * q = 1)
include hx hv hp hq

lemma algE0 : Ug z p q 0 = 1 + x * Ug z p q 0 + x ^ 2 * Rg x z p q 0 := by
  subst hx; simp only [Ug, Rg, Rt, uu]
  linear_combination (q*v^5*z^15 + 4*q*v^5*z^14 + 12*q*v^5*z^13 + 23*q*v^5*z^12 + 39*q*v^5*z^11 + 54*q*v^5*z^10 + 72*q*v^5*z^9 + 81*q*v^5*z^8 + 81*q*v^5*z^7 + 61*q*v^5*z^6 + 35*q*v^5*z^5 + 9*q*v^5*z^4 - 3*q*v^5*z^3 - 6*q*v^5*z^2 - 3*q*v^5*z - q*v^5 + q*v^4*z^13 + 3*q*v^4*z^12 + 8*q*v^4*z^11 + 12*q*v^4*z^10 + 18*q*v^4*z^9 + 21*q*v^4*z^8 + 27*q*v^4*z^7 + 26*q*v^4*z^6 + 22*q*v^4*z^5 + 10*q*v^4*z^4 + 2*q*v^4*z^3 - 3*q*v^4*z^2 - 2*q*v^4*z - q*v^4 + q*v^3*z^11 + 2*q*v^3*z^10 + 5*q*v^3*z^9 + 5*q*v^3*z^8 + 8*q*v^3*z^7 + 7*q*v^3*z^6 + 10*q*v^3*z^5 + 6*q*v^3*z^4 + 4*q*v^3*z^3 - q*v^3*z^2 - q*v^3*z - q*v^3 + q*v^2*z^9 + q*v^2*z^8 + 3*q*v^2*z^7 + 2*q*v^2*z^6 + 4*q*v^2*z^5 + 2*q*v^2*z^4 + 3*q*v^2*z^3 - q*v^2 + q*v*z^7 + 3*q*v*z^5 + 3*q*v*z^3 - q*v*z^2 + q*v*z - q*v + q*z^5 + 2*q*z^3 + q*z - q + v^5*z^10 + 5*v^5*z^9 + 15*v^5*z^8 + 30*v^5*z^7 + 45*v^5*z^6 + 51*v^5*z^5 + 45*v^5*z^4 + 30*v^5*z^3 + 15*v^5*z^2 + 5*v^5*z + v^5 + v^4*z^8 + 4*v^4*z^7 + 10*v^4*z^6 + 16*v^4*z^5 + 19*v^4*z^4 + 16*v^4*z^3 + 10*v^4*z^2 + 4*v^4*z + v^4 + v^3*z^6 + 3*v^3*z^5 + 6*v^3*z^4 + 7*v^3*z^3 + 6*v^3*z^2 + 3*v^3*z + v^3 + v^2*z^4 + 2*v^2*z^3 + 3*v^2*z^2 + 2*v^2*z + v^2 + v*z^2 + v*z + v + 1) * hv + (q*v^6*z^17 + 5*q*v^6*z^16 + 17*q*v^6*z^15 + 39*q*v^6*z^14 + 74*q*v^6*z^13 + 116*q*v^6*z^12 + 165*q*v^6*z^11 + 207*q*v^6*z^10 + 234*q*v^6*z^9 + 223*q*v^6*z^8 + 177*q*v^6*z^7 + 105*q*v^6*z^6 + 41*q*v^6*z^5 - 12*q*v^6*z^3 - 10*q*v^6*z^2 - 4*q*v^6*z - q*v^6 + v^6*z^12 + 6*v^6*z^11 + 21*v^6*z^10 + 50*v^6*z^9 + 90*v^6*z^8 + 126*v^6*z^7 + 141*v^6*z^6 + 126*v^6*z^5 + 90*v^6*z^4 + 50*v^6*z^3 + 21*v^6*z^2 + 6*v^6*z + v^6) * hp + (p*v^6*z^13 + 7*p*v^6*z^12 + 27*p*v^6*z^11 + 71*p*v^6*z^10 + 140*p*v^6*z^9 + 216*p*v^6*z^8 + 267*p*v^6*z^7 + 267*p*v^6*z^6 + 216*p*v^6*z^5 + 140*p*v^6*z^4 + 71*p*v^6*z^3 + 27*p*v^6*z^2 + 7*p*v^6*z + p*v^6) * hq

omit hq in
lemma algE1 : Ug z p q 1 = Ug z p q 0 + x * Ug z p q 1 + x ^ 2 * Rg x z p q 1 := by
  subst hx; simp only [Ug, Rg, Rt, uu]
  linear_combination (-q*v^4*z^11 - 3*q*v^4*z^10 - 6*q*v^4*z^9 - 7*q*v^4*z^8 - 6*q*v^4*z^7 - 3*q*v^4*z^6 - q*v^4*z^5 - q*v^3*z^9 - 3*q*v^3*z^8 - 5*q*v^3*z^7 - 5*q*v^3*z^6 - 3*q*v^3*z^5 - q*v^3*z^4 - q*v^2*z^7 - 2*q*v^2*z^6 - 3*q*v^2*z^5 - 2*q*v^2*z^4 - q*v^2*z^3 - q*v*z^4 - q*v*z^3 - q*v*z^2 + q*z^4 - q*z) * hv + (-q*v^5*z^13 - 4*q*v^5*z^12 - 10*q*v^5*z^11 - 16*q*v^5*z^10 - 19*q*v^5*z^9 - 16*q*v^5*z^8 - 10*q*v^5*z^7 - 4*q*v^5*z^6 - q*v^5*z^5) * hp

omit hq in
lemma algE2 : Ug z p q 2 = Ug z p q 1 + x * Ug z p q 2 + x ^ 2 * Rg x z p q 2 := by
  subst hx; simp only [Ug, Rg, Rt, uu]
  linear_combination (-q*v^3*z^10 - 3*q*v^3*z^9 - 6*q*v^3*z^8 - 7*q*v^3*z^7 - 6*q*v^3*z^6 - 3*q*v^3*z^5 - q*v^3*z^4 - q*v^2*z^8 - 3*q*v^2*z^7 - 5*q*v^2*z^6 - 5*q*v^2*z^5 - 3*q*v^2*z^4 - q*v^2*z^3 - q*v*z^6 - 2*q*v*z^5 - 3*q*v*z^4 - 2*q*v*z^3 - q*v*z^2 - q*z^3 - q*z^2 - q*z) * hv + (-q*v^4*z^12 - 4*q*v^4*z^11 - 10*q*v^4*z^10 - 16*q*v^4*z^9 - 19*q*v^4*z^8 - 16*q*v^4*z^7 - 10*q*v^4*z^6 - 4*q*v^4*z^5 - q*v^4*z^4) * hp

omit hq in
lemma algE3 : Ug z p q 3 = Ug z p q 2 + x * Ug z p q 3 + x ^ 2 * Rg x z p q 3 := by
  subst hx; simp only [Ug, Rg, Rt, uu]
  linear_combination (-q*v^2*z^9 - 3*q*v^2*z^8 - 6*q*v^2*z^7 - 7*q*v^2*z^6 - 6*q*v^2*z^5 - 3*q*v^2*z^4 - q*v^2*z^3 - q*v*z^7 - 3*q*v*z^6 - 5*q*v*z^5 - 5*q*v*z^4 - 3*q*v*z^3 - q*v*z^2 - q*z^5 - 2*q*z^4 - 3*q*z^3 - 2*q*z^2 - q*z) * hv + (-q*v^3*z^11 - 4*q*v^3*z^10 - 10*q*v^3*z^9 - 16*q*v^3*z^8 - 19*q*v^3*z^7 - 16*q*v^3*z^6 - 10*q*v^3*z^5 - 4*q*v^3*z^4 - q*v^3*z^3) * hp

omit hq in
lemma algE4 : Ug z p q 4 = Ug z p q 3 + x * Ug z p q 4 + x ^ 2 * Rg x z p q 4 := by
  subst hx; simp only [Ug, Rg, Rt, uu]
  linear_combination (-q*v*z^8 - 3*q*v*z^7 - 6*q*v*z^6 - 7*q*v*z^5 - 6*q*v*z^4 - 3*q*v*z^3 - q*v*z^2 - q*z^6 - 3*q*z^5 - 5*q*z^4 - 5*q*z^3 - 3*q*z^2 - q*z) * hv + (-q*v^2*z^10 - 4*q*v^2*z^9 - 10*q*v^2*z^8 - 16*q*v^2*z^7 - 19*q*v^2*z^6 - 16*q*v^2*z^5 - 10*q*v^2*z^4 - 4*q*v^2*z^3 - q*v^2*z^2) * hp

omit hq in
lemma core1 : uu z * p = 1 + x ^ 2 * (uu z * p) ^ 2 * (1 + z) := by
  subst hx; simp only [uu]
  linear_combination (-p*v*z^4 - 2*p*v*z^3 - 3*p*v*z^2 - 2*p*v*z - p*v - p*z^2 - p*z - p + v*z^2 + v*z + v + 1) * hv + (-p*v^2*z^6 - 2*p*v^2*z^5 - 3*p*v^2*z^4 - 2*p*v^2*z^3 - p*v^2*z^2 + v^2*z^4 + 2*v^2*z^3 + 3*v^2*z^2 + 2*v^2*z + v^2) * hp

omit hq in
lemma core2 : 1 + z = 1 + x * (uu z * p) * (1 + z) := by
  subst hx; simp only [uu]
  linear_combination (-z) * hv + (-v*z^3 - v*z^2 - v*z) * hp

omit hq in
lemma algE5 (k : ℕ) :
    Ug z p q (k + 5) = Ug z p q (k + 4) + x ^ 2 * Rg x z p q (k + 5) := by
  have h := core1 x z v p hx hv hp
  simp only [Ug, Rg, Rt]
  linear_combination (uu z ^ 3 * q * (uu z * p) ^ k) * h

omit hq in
lemma algT (k : ℕ) : Rg x z p q (k + 4) = Ug z p q (k + 5) + x * Rg x z p q (k + 5) := by
  have h := core2 x z v p hx hv hp
  simp only [Ug, Rg, Rt]
  linear_combination (uu z ^ 3 * q * (uu z * p) ^ (k + 1)) * h

end Alg

/-! Power series instances. -/

noncomputable def vS : ℚ⟦X⟧ := (1 + zM + zM ^ 2)⁻¹
noncomputable def pS : ℚ⟦X⟧ := (1 + zM)⁻¹
noncomputable def qS : ℚ⟦X⟧ := (QQ zM)⁻¹

lemma hv : (1 + zM + zM ^ 2) * vS = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp [constantCoeff_zM])
lemma hp : (1 + zM) * pS = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp [constantCoeff_zM])
lemma hq : (1 - 2 * zM + zM ^ 2 - 2 * zM ^ 3 + zM ^ 4 - zM ^ 5) * qS = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp [constantCoeff_zM])
lemma hX : (X : ℚ⟦X⟧) = zM * vS := by
  have h := hv
  calc (X : ℚ⟦X⟧) = X * ((1 + zM + zM ^ 2) * vS) := by rw [h, mul_one]
    _ = zM * vS := by rw [← mul_assoc, ← zM_eq]

noncomputable def V (j : ℕ) : ℚ⟦X⟧ := X ^ j * Ug zM pS qS j
noncomputable def T (j : ℕ) : ℚ⟦X⟧ := X ^ (j + 1) * Rg X zM pS qS j

lemma D0 : V 0 = 1 + X * (V 0 + T 0) := by
  have h := algE0 X zM vS pS qS hX hv hp hq
  simp only [V, T]; linear_combination h

lemma D1 (i : ℕ) (hi : i ≤ 3) : V (i + 1) = X * (V i + V (i + 1) + T (i + 1)) := by
  simp only [V, T]
  interval_cases i <;> simp only [Nat.reduceAdd, zero_add]
  · linear_combination X * algE1 X zM vS pS qS hX hv hp
  · linear_combination X ^ 2 * algE2 X zM vS pS qS hX hv hp
  · linear_combination X ^ 3 * algE3 X zM vS pS qS hX hv hp
  · linear_combination X ^ 4 * algE4 X zM vS pS qS hX hv hp

lemma D2 (k : ℕ) : V (k + 5) = X * (V (k + 4) + T (k + 5)) := by
  simp only [V, T]
  linear_combination X ^ (k + 5) * algE5 X zM vS pS qS hX hv hp k

lemma DT (j : ℕ) : T j = V (j + 1) + T (j + 1) := by
  simp only [V, T]
  rcases (show j ≤ 3 ∨ 4 ≤ j by omega) with h | h
  · interval_cases j <;> simp only [Rg] <;> ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
    linear_combination X ^ (k + 5) * algT X zM vS pS qS hX hv hp k

lemma T_tele (j m : ℕ) : T j = ∑ i ∈ Ioc j (j + m), V i + T (j + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, DT (j + m), ← add_assoc, show j + (m + 1) = j + m + 1 by omega,
      Finset.sum_Ioc_succ_top (by omega)]

lemma coeff_V_high {n j : ℕ} (h : n < j) : coeff n (V j) = 0 := by
  simp [V, coeff_X_pow_mul', show ¬ j ≤ n by omega]

lemma coeff_T_high {n j : ℕ} (h : n ≤ j) : coeff n (T j) = 0 := by
  simp [T, coeff_X_pow_mul', show ¬ j + 1 ≤ n by omega]

lemma coeff_T (n j : ℕ) : coeff n (T j) = ∑ i ∈ Ioc j n, coeff n (V i) := by
  rw [T_tele j n, map_add, coeff_T_high (by omega), add_zero, map_sum]
  symm
  apply Finset.sum_subset
  · intro i hi; simp only [Finset.mem_Ioc] at hi ⊢; omega
  · intro i hi hi'
    simp only [Finset.mem_Ioc] at hi hi'
    exact coeff_V_high (by omega)

lemma coeff_V (n : ℕ) : ∀ j, coeff n (V j) = (w n j : ℚ) := by
  induction n with
  | zero =>
    intro j
    rcases j with _ | j
    · rw [D0]; simp [w]
    · rw [coeff_V_high (by omega)]; simp [w]
  | succ n ih =>
    intro j
    have hT : coeff n (T j) = ∑ i ∈ Ioc j n, (w n i : ℚ) := by
      rw [coeff_T]; exact Finset.sum_congr rfl (fun i _ => ih i)
    rcases (show j = 0 ∨ (1 ≤ j ∧ j ≤ 4) ∨ 5 ≤ j by omega) with h | ⟨h1, h2⟩ | h
    · subst h
      rw [D0, map_add, coeff_succ_X_mul, map_add, ih, hT]
      simp [w]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [D1 i (by omega), coeff_succ_X_mul, map_add, map_add, ih, ih, hT]
      simp [w, show i + 1 ≤ 4 from h2]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
      rw [D2 k, coeff_succ_X_mul, map_add, ih, hT]
      simp [w, show ¬ k + 5 ≤ 4 by omega]

/-- Generating function of A152718 times its denominator. -/
lemma gfB : mk (fun n => (A152718 n : ℚ)) * (1 - 2 * X + X ^ 2 - 2 * X ^ 3 + X ^ 4 - X ^ 5)
    = 1 - X - 2 * X ^ 3 - X ^ 5 := by
  set f := mk (fun n => (A152718 n : ℚ))
  have e1 : f * (1 - 2 * X + X ^ 2 - 2 * X ^ 3 + X ^ 4 - X ^ 5) = f - X ^ 1 * f - X ^ 1 * f +
      X ^ 2 * f - X ^ 3 * f - X ^ 3 * f + X ^ 4 * f - X ^ 5 * f := by ring
  have e2 : (1 - X - 2 * X ^ 3 - X ^ 5 : ℚ⟦X⟧) = X ^ 0 - X ^ 1 - X ^ 3 - X ^ 3 - X ^ 5 := by ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_X_pow_mul', coeff_X_pow, f, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | m
  all_goals norm_num [A152718]
  ring

lemma subst_eq : (mk fun n => (A152718 n : ℚ)).subst zM = Ug zM pS qS 0 := by
  have hs : HasSubst zM := HasSubst.of_constantCoeff_zero' constantCoeff_zM
  have h := congrArg (substAlgHom (R := ℚ) hs) gfB
  simp only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, substAlgHom_X,
    coe_substAlgHom] at h
  have h2 : (mk fun n => (A152718 n : ℚ)).subst zM =
      (mk fun n => (A152718 n : ℚ)).subst zM *
        ((1 - 2 * zM + zM ^ 2 - 2 * zM ^ 3 + zM ^ 4 - zM ^ 5) * qS) := by rw [hq, mul_one]
  rw [h2, ← mul_assoc, h]
  simp only [Ug, uu]; ring

/-- Main theorem, series form: A054393(x) = A152718(z) with z = x M(x). -/
theorem A152718_motzkin :
    mk (fun n => (A054393 n : ℚ)) = (mk fun n => (A152718 n : ℚ)).subst zM := by
  ext n
  rw [subst_eq, coeff_mk, A054393, ← coeff_V n 0]
  simp [V]

lemma coeff_zM_pow_high {n d : ℕ} (h : n < d) : coeff n (zM ^ d) = 0 := by
  rw [zM_eq, mul_pow, coeff_X_pow_mul']
  simp [show ¬ d ≤ n by omega]

/-- Main theorem, coefficient form: a054393(n) = sum_{k=0}^n a152718(k) [x^n] (x M(x))^k. -/
theorem A152718_motzkin_coeff (n : ℕ) :
    (A054393 n : ℚ) = ∑ k ∈ range (n + 1), (A152718 k : ℚ) * coeff n (zM ^ k) := by
  have hs : HasSubst zM := HasSubst.of_constantCoeff_zero' constantCoeff_zM
  have := congrArg (coeff n) A152718_motzkin
  rw [coeff_mk, coeff_subst' hs] at this
  rw [this, finsum_eq_sum_of_support_subset _ (s := range (n + 1))]
  · simp [coeff_mk, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, coe_range, Set.mem_Iio] at hd ⊢
    by_contra h'
    exact hd (by rw [coeff_zM_pow_high (by omega), smul_zero])

end OEIS152718

open OEIS152718
