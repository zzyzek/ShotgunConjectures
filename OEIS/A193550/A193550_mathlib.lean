/-
OEIS A193550: o.g.f. A(x) = 1/(1 - x/(1 - x/(1 - 9x/(1 - 9x/(1 - 25x/(1 - 25x/ ...)))))),
the continued fraction with partial numerators lam i = (2*(i/2)+1)^2 = 1, 1, 9, 9, 25, 25, ...
Conjecture (Paul D. Hanna): sqrt((A(x) - 1)/x) is an integer series.

Checked here (Lean + Mathlib, no sorry, no native_decide):
* `A193550_conjecture`: there is B in Z[[x]] with B(0) = 1 and A = 1 + x * B^2,
  where A = mk a and a n is the x^n coefficient of the depth-(n+1) truncation of the
  continued fraction (as in the PARI program of the entry).
* `a_eq_deeper`: a n equals the x^n coefficient of every deeper truncation, so `a` is the
  coefficient sequence of the infinite continued fraction.
Route: every lam i = 1 (mod 4), so A = Catalan series (mod 4) (`a_mod4`); hence
(A - 1)/x = C^2 + 4H with C the Catalan series, and sqrt(1 + 4y) is integral for y(0) = 0
(`quad_root`: W + W^2 = y has an integer solution).
Declarations live in namespace A193550 (left open so the axiom check can name them).
Not checked in Lean: agreement of `a` with the OEIS data (certificate/check.py).
-/
import Mathlib

open PowerSeries

namespace A193550

/-- Partial numerators 1, 1, 9, 9, 25, 25, ... (index from 0). -/
def lam (i : ℕ) : ℤ := (2 * ((i / 2 : ℕ) : ℤ) + 1) ^ 2

/-- Depth-m truncation of the continued fraction from level j:
`T 0 j = 1`, `T (m+1) j = 1 / (1 - lam j * x * T m (j+1))`. -/
noncomputable def T : ℕ → ℕ → PowerSeries ℤ
  | 0, _ => 1
  | m + 1, j => invOfUnit (1 - C (lam j) * X * T m (j + 1)) 1

/-- OEIS A193550: a n is the x^n coefficient of the continued fraction. -/
noncomputable def a (n : ℕ) : ℤ := coeff n (T (n + 1) 0)

lemma constT (m j : ℕ) : constantCoeff (T m j) = 1 := by
  cases m with
  | zero => simp [T]
  | succ m => simp [T, constantCoeff_invOfUnit]

lemma mulT (m j : ℕ) : (1 - C (lam j) * X * T m (j + 1)) * T (m + 1) j = 1 := by
  apply mul_invOfUnit
  simp

lemma inv_sub {R : Type*} [CommRing R] {a a' b b' : R} (ha : a * a' = 1) (hb : b * b' = 1) :
    a' - b' = a' * b' * (b - a) := by
  linear_combination (-a') * hb + b' * ha

lemma stab (m j : ℕ) : (X : PowerSeries ℤ) ^ m ∣ T (m + 1) j - T m j := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [inv_sub (mulT (m + 1) j) (mulT m j)]
    obtain ⟨q, hq⟩ := ih (j + 1)
    refine ⟨T (m + 2) j * T (m + 1) j * C (lam j) * q, ?_⟩
    have : (1 - C (lam j) * X * T m (j + 1)) - (1 - C (lam j) * X * T (m + 1) (j + 1)) =
        C (lam j) * X * (T (m + 1) (j + 1) - T m (j + 1)) := by ring
    rw [this, hq]
    ring

lemma stab_of {R : Type*} [CommRing R] {f : ℕ → PowerSeries R}
    (h : ∀ m, (X : PowerSeries R) ^ m ∣ f (m + 1) - f m) (n d : ℕ) :
    coeff n (f (n + 1 + d)) = coeff n (f (n + 1)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h1 := (X_pow_dvd_iff.mp (h (n + 1 + d))) n (by omega)
    rw [map_sub, sub_eq_zero] at h1
    rw [← ih, ← h1]
    rfl

/-- `a n` is the x^n coefficient of every truncation of depth > n. -/
theorem a_eq_deeper (n m : ℕ) (h : n < m) : a n = coeff n (T m 0) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + 1 + d := ⟨m - (n + 1), by omega⟩
  exact (stab_of (f := fun m => T m 0) (fun m => stab m 0) n d).symm

/-! ### Reduction mod 4 -/

lemma lam_mod (j : ℕ) : ((lam j : ℤ) : ZMod 4) = 1 := by
  have key : ∀ x : ZMod 4, (2 * x + 1) ^ 2 = 1 := by decide
  simp only [lam]
  push_cast
  exact key _

/-- Catalan series in Z/4. -/
noncomputable def Cb : PowerSeries (ZMod 4) := map (Nat.castRingHom (ZMod 4)) catalanSeries

lemma Cb_eq : (1 - X * Cb) * Cb = 1 := by
  have h := congrArg (map (Nat.castRingHom (ZMod 4))) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_X, map_one] at h
  rw [Cb]
  linear_combination -h

lemma mod4 (m j : ℕ) :
    (X : PowerSeries (ZMod 4)) ^ m ∣ map (Int.castRingHom (ZMod 4)) (T m j) - Cb := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    have hA : (1 - X * map (Int.castRingHom (ZMod 4)) (T m (j + 1))) *
        map (Int.castRingHom (ZMod 4)) (T (m + 1) j) = 1 := by
      have h := congrArg (map (Int.castRingHom (ZMod 4))) (mulT m j)
      simp only [map_mul, map_sub, map_one, map_C, map_X] at h
      rw [show (Int.castRingHom (ZMod 4)) (lam j) = 1 from by simpa using lam_mod j] at h
      simp only [map_one, one_mul] at h
      linear_combination h
    rw [inv_sub hA Cb_eq]
    obtain ⟨q, hq⟩ := ih (j + 1)
    refine ⟨map (Int.castRingHom (ZMod 4)) (T (m + 1) j) * Cb * q, ?_⟩
    have : (1 - X * Cb) - (1 - X * map (Int.castRingHom (ZMod 4)) (T m (j + 1))) =
        X * (map (Int.castRingHom (ZMod 4)) (T m (j + 1)) - Cb) := by ring
    rw [this, hq]
    ring

lemma a_mod4 (n : ℕ) : ((a n : ℤ) : ZMod 4) = ((catalan n : ℕ) : ZMod 4) := by
  have h := (X_pow_dvd_iff.mp (mod4 (n + 1) 0)) n (by omega)
  rw [map_sub, sub_eq_zero, coeff_map, Cb, coeff_map, catalanSeries_coeff] at h
  simpa [a] using h

lemma coeff_one_T (m j : ℕ) : coeff 1 (T (m + 1) j) = lam j := by
  have h := congrArg (coeff 1) (mulT m j)
  rw [coeff_mul, Finset.Nat.antidiagonal_succ] at h
  simp [coeff_one, mul_assoc, constT] at h
  linear_combination h

lemma a_zero : a 0 = 1 := by
  simp [a, coeff_zero_eq_constantCoeff_apply, constT]

lemma a_one : a 1 = 1 := by
  rw [a, coeff_one_T]
  simp [lam]

/-! ### Square roots of 1 + 4y -/

/-- Iteration w_0 = 0, w_(k+1) = y - w_k^2. -/
noncomputable def wIt (y : PowerSeries ℤ) : ℕ → PowerSeries ℤ
  | 0 => 0
  | k + 1 => y - wIt y k ^ 2

/-- Limit of the iteration: x^n coefficient of w_(n+1). -/
noncomputable def wLim (y : PowerSeries ℤ) : PowerSeries ℤ := mk fun n => coeff n (wIt y (n + 1))

/-- If y(0) = 0 then W + W^2 = y has a solution in Z[[x]] with W(0) = 0. -/
lemma quad_root (y : PowerSeries ℤ) (hy : constantCoeff y = 0) :
    ∃ W : PowerSeries ℤ, constantCoeff W = 0 ∧ W + W ^ 2 = y := by
  have w0 : wIt y 0 = 0 := rfl
  have ws : ∀ k, wIt y (k + 1) = y - wIt y k ^ 2 := fun _ => rfl
  have wX : ∀ k, (X : PowerSeries ℤ) ∣ wIt y k := by
    intro k
    induction k with
    | zero => simp [w0]
    | succ k ih =>
      rw [ws]
      exact dvd_sub (X_dvd_iff.mpr hy) (dvd_pow ih (by norm_num))
  have wstep : ∀ k, (X : PowerSeries ℤ) ^ (k + 1) ∣ wIt y (k + 1) - wIt y k := by
    intro k
    induction k with
    | zero => simpa [ws, w0] using X_dvd_iff.mpr hy
    | succ k ih =>
      have : wIt y (k + 2) - wIt y (k + 1) = -((wIt y (k + 1) - wIt y k) * (wIt y (k + 1) + wIt y k)) := by
        rw [ws (k + 1), ws k]; ring
      rw [this, pow_succ]
      exact (mul_dvd_mul ih (dvd_add (wX _) (wX _))).neg_right
  have wstep' : ∀ k, (X : PowerSeries ℤ) ^ k ∣ wIt y (k + 1) - wIt y k :=
    fun k => (pow_dvd_pow _ (Nat.le_succ k)).trans (wstep k)
  set W : PowerSeries ℤ := wLim y with hWdef
  have hWn : ∀ n, (X : PowerSeries ℤ) ^ (n + 1) ∣ W - wIt y (n + 1) := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hWdef, wLim, coeff_mk, sub_eq_zero]
    obtain ⟨d, hd⟩ : ∃ d, n + 1 = m + 1 + d := ⟨n - m, by omega⟩
    rw [hd, stab_of (f := wIt y) wstep' m d]
  refine ⟨W, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, hWdef, wLim, coeff_mk, ws, w0]
    simp [coeff_zero_eq_constantCoeff_apply, hy]
  · ext n
    have h1 : (X : PowerSeries ℤ) ^ (n + 1) ∣ W + W ^ 2 - y := by
      obtain ⟨q, hq⟩ := hWn n
      obtain ⟨r, hr⟩ := wstep (n + 1)
      refine ⟨q * (1 + W + wIt y (n + 1)) - X * r, ?_⟩
      have e : W + W ^ 2 - y = (W - wIt y (n + 1)) * (1 + W + wIt y (n + 1)) -
          (wIt y (n + 2) - wIt y (n + 1)) := by rw [ws (n + 1)]; ring
      rw [e, hq, hr]
      ring
    have h2 := (X_pow_dvd_iff.mp h1) n (by omega)
    rwa [map_sub, sub_eq_zero] at h2

/-! ### Main theorem -/

/-- Catalan series over Z. -/
noncomputable def CZ : PowerSeries ℤ := map (Nat.castRingHom ℤ) catalanSeries

lemma CZ_eq : CZ ^ 2 * X + 1 = CZ := by
  have h := congrArg (map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_X, map_one] at h
  exact h

lemma coeff_CZ (n : ℕ) : coeff n CZ = (catalan n : ℤ) := by
  simp [CZ, coeff_map, catalanSeries_coeff]

lemma coeff_CZ_sq (n : ℕ) : coeff n (CZ ^ 2) = (catalan (n + 1) : ℤ) := by
  have h := congrArg (coeff (n + 1)) CZ_eq
  rw [map_add, mul_comm, coeff_succ_X_mul, coeff_one, coeff_CZ] at h
  simpa using h

/-- The conjecture: A(x) = 1 + x * B(x)^2 with B an integer series, B(0) = 1. -/
theorem A193550_conjecture :
    ∃ B : PowerSeries ℤ, constantCoeff B = 1 ∧ mk a = 1 + X * B ^ 2 := by
  have hdiv : ∀ n, (4 : ℤ) ∣ a (n + 1) - catalan (n + 1) := by
    intro n
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (a (n + 1) - catalan (n + 1)) 4).mp
      (by push_cast; rw [a_mod4]; simp)
    exact_mod_cast h
  let H : PowerSeries ℤ := mk fun n => (a (n + 1) - catalan (n + 1)) / 4
  have hF : (mk fun n => a (n + 1)) = CZ ^ 2 + 4 * H := by
    ext n
    have h4 : (4 : PowerSeries ℤ) = C (4 : ℤ) := (map_ofNat C 4).symm
    rw [h4, map_add, coeff_C_mul, coeff_mk, coeff_mk, coeff_CZ_sq, Int.mul_ediv_cancel' (hdiv n)]
    ring
  have hH0 : constantCoeff H = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, a_one]
    simp
  have hC1 : constantCoeff CZ = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_CZ]
    simp
  set Ci := invOfUnit CZ 1
  have hC : CZ * Ci = 1 := mul_invOfUnit CZ 1 hC1
  obtain ⟨W, hW0, hW⟩ := quad_root (H * Ci ^ 2) (by simp [hH0])
  refine ⟨CZ * (1 + 2 * W), ?_, ?_⟩
  · rw [map_mul, hC1, map_add, map_mul, hW0]
    simp
  · have hA : mk a = 1 + X * mk fun n => a (n + 1) := by
      ext n
      cases n with
      | zero => rw [coeff_mk, map_add, coeff_one, coeff_zero_X_mul, a_zero]; rfl
      | succ n =>
        rw [coeff_mk, map_add, coeff_one, coeff_succ_X_mul, coeff_mk]
        simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_add]
    rw [hA, hF]
    linear_combination (-X) * ((4 * CZ ^ 2) * hW + 4 * H * (CZ * Ci + 1) * hC)
