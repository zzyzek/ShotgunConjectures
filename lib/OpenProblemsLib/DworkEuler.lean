import Mathlib
import OpenProblemsLib.Dwork

/-!
# The bivariate Euler-product lemma, in coefficient form

Paper lemma (OEIS/A183241/README.md, item 4): for `H ∈ 1 + ℤ[[x, y]]` and the linear map
`Φ : x^m y^n ↦ w(m,n) x^m`, `exp (Φ (log H))` is an integer series when the weights are Gauss
sequences along every ray.  All instances in this repo have `H = 1 / (1 - y F)`, so
`log H = ∑_n y^n F^n / n` is explicit and the `x`-log-derivative of `exp (Φ log H)` is the
integer sequence

  `rowB F y W m = ∑_{n ≤ m} W m n * (m / n) * [x^m] F^n`.

To also cover the three-variable form used for A163138, `F` lives in `ℤ[Y][X]`
(`Polynomial (Polynomial ℤ)`), and the `Y`-coefficient polynomial `[x^m] F^n ∈ ℤ[Y]` is evaluated
at an integer `y n` that may depend on `n`. One-variable instances take `F` constant in `Y`
(`Polynomial.map C f`) and `y = 0`.

Main results (namespace `OpenProblemsLib.DworkEuler`).
* `frob_pow_congr`: `p^(e+1) ∣ F^(p k) - (frobLift p F)^k` in `ℤ[Y][X]` when `p^e ∣ k`, where
  `frobLift p` substitutes `X ↦ X^p`, `Y ↦ Y^p` (Frobenius lift).
* `dvd_m_mul_coeff`: `p^e ∣ n → p^e ∣ m * [x^m] F^n` (in `ℤ[Y]`); with `V_mul`:
  `V F y m n := m * ([x^m] F^n)(y n) / n` is an exact integer quotient.
* `V0`, `V1`: the ray congruences of `V`: `p^k ∣ m`, `p^(s+1) ∤ n ⇒ p^(k-s) ∣ V m n`, and
  `p^k ∣ m ⇒ p^(k+1) ∣ V (p m) (p n) - V m n`.
* `W1 p W`: the weight condition `p^k ∣ m, p^k ∣ n ⇒ p^(k+1) ∣ W (p m) (p n) - W m n`
  (Gauss congruences along every ray); `W1_pow`: `W m n = u n ^ κ m n` satisfies it when `u` is a
  Gauss sequence, `κ (p m) (p n) = p κ m n` and `p^k ∣ m, n ⇒ p^k ∣ κ m n` (covers `L(n)^(m-n)`,
  `q^(n(m-n))`, `q^(m n)`); `W1_one`.
* `rowsum_gauss`: a two-index array with `T0`/`T1` has Gauss row sums `m ↦ ∑_{n ≤ m} T m n`.
* `rowB_gauss`, `rowB_int` (the bivariate Euler-product lemma): `expCoeff (rowB F y W) N ∈ ℤ`.
* `ycond_zero`, `ycond_pow`: the admissible evaluation points `y n = 0` and `y n = q^n`.
-/

namespace OpenProblemsLib.DworkEuler

open Polynomial OpenProblemsLib.Dwork

/-! ## Frobenius lift on `ℤ[Y][X]` -/

/-- `X ↦ X^p`, `Y ↦ Y^p`. -/
noncomputable def frobLift (p : ℕ) : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℤ) :=
  (expand (Polynomial ℤ) p).toRingHom.comp (mapRingHom (expand ℤ p).toRingHom)

/-- The same over `ZMod p`. -/
noncomputable def frobLiftZ (p : ℕ) :
    Polynomial (Polynomial (ZMod p)) →+* Polynomial (Polynomial (ZMod p)) :=
  (expand (Polynomial (ZMod p)) p).toRingHom.comp (mapRingHom (expand (ZMod p) p).toRingHom)

/-- Reduction mod `p` of both coefficient layers. -/
noncomputable def red (p : ℕ) : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial (ZMod p)) :=
  mapRingHom (mapRingHom (Int.castRingHom (ZMod p)))

theorem frobLiftZ_eq_pow (p : ℕ) (hp : p.Prime) (f : Polynomial (Polynomial (ZMod p))) :
    frobLiftZ p f = f ^ p := by
  have := Fact.mk hp
  have h : frobLiftZ p = frobenius (Polynomial (Polynomial (ZMod p))) p := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [frobLiftZ, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, expand_C, frobenius_def, ← C_pow]
      rw [ZMod.expand_card]
    · simp [frobLiftZ, frobenius_def]
  rw [h, frobenius_def]

theorem red_frobLift (p : ℕ) (F : Polynomial (Polynomial ℤ)) :
    red p (frobLift p F) = frobLiftZ p (red p F) := by
  have h : (red p).comp (frobLift p) = (frobLiftZ p).comp (red p) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [red, frobLift, frobLiftZ, map_expand]
    · simp [red, frobLift, frobLiftZ]
  exact congrArg (fun φ => φ F) h

theorem dvd_of_red_eq_zero (p : ℕ) (G : Polynomial (Polynomial ℤ)) (h : red p G = 0) :
    (p : Polynomial (Polynomial ℤ)) ∣ G := by
  rw [← map_natCast (C : Polynomial ℤ →+* _), C_dvd_iff_dvd_coeff]
  intro i
  rw [← map_natCast (C : ℤ →+* _), C_dvd_iff_dvd_coeff]
  intro j
  have := congrArg (fun g => (g.coeff i).coeff j) h
  simp only [red, coe_mapRingHom, coeff_map, eq_intCast, coeff_zero] at this
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa using this

theorem frob_mod (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) :
    (p : Polynomial (Polynomial ℤ)) ∣ F ^ p - frobLift p F := by
  apply dvd_of_red_eq_zero
  rw [map_sub, map_pow, red_frobLift, frobLiftZ_eq_pow p hp, sub_self]

/-- Frobenius congruence, lifted: `p^(e+1) ∣ F^(p k) - (frobLift p F)^k` when `p^e ∣ k`. -/
theorem frob_pow_congr (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) (e k : ℕ)
    (hk : p ^ e ∣ k) :
    (p : Polynomial (Polynomial ℤ)) ^ (e + 1) ∣ F ^ (p * k) - frobLift p F ^ k := by
  obtain ⟨t, rfl⟩ := hk
  have h1 := dvd_sub_pow_of_dvd_sub (frob_mod p hp F) e
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ t)
  have e1 : F ^ (p * (p ^ e * t)) = ((F ^ p) ^ p ^ e) ^ t := by
    rw [← pow_mul, ← pow_mul]
  have e2 : frobLift p F ^ (p ^ e * t) = (frobLift p F ^ p ^ e) ^ t := by rw [← pow_mul]
  rw [e1, e2]; exact h2

theorem coeff_frobLift_pow (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) (k i : ℕ) :
    (frobLift p F ^ k).coeff i =
      if p ∣ i then expand ℤ p ((F ^ k).coeff (i / p)) else 0 := by
  rw [← map_pow]
  simp only [frobLift, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, coeff_expand hp.pos, coe_mapRingHom, coeff_map]

theorem natCast_pow_eq_C (p r : ℕ) :
    (p : Polynomial (Polynomial ℤ)) ^ r = C ((p : Polynomial ℤ) ^ r) := by
  rw [map_pow, map_natCast]

theorem coeff_dvd_of_dvd (p r : ℕ) (G : Polynomial (Polynomial ℤ))
    (h : (p : Polynomial (Polynomial ℤ)) ^ r ∣ G) (i : ℕ) :
    (p : Polynomial ℤ) ^ r ∣ G.coeff i := by
  obtain ⟨H, rfl⟩ := h
  rw [natCast_pow_eq_C, coeff_C_mul]
  exact dvd_mul_right _ _

theorem eval_dvd_of_dvd (p r : ℕ) (P : Polynomial ℤ) (h : (p : Polynomial ℤ) ^ r ∣ P) (y : ℤ) :
    (p : ℤ) ^ r ∣ P.eval y := by
  obtain ⟨H, rfl⟩ := h
  rw [eval_mul, eval_pow, eval_natCast]
  exact dvd_mul_right _ _

theorem expand_dvd_of_dvd (p r : ℕ) (P : Polynomial ℤ) (h : (p : Polynomial ℤ) ^ r ∣ P) :
    (p : Polynomial ℤ) ^ r ∣ expand ℤ p P := by
  obtain ⟨H, rfl⟩ := h
  rw [map_mul, map_pow, map_natCast]
  exact dvd_mul_right _ _

/-! ## The coefficient array `P m n = [x^m] F^n ∈ ℤ[Y]` -/

/-- `p^e ∣ n ⇒ p^e ∣ m * [x^m] F^n`. -/
theorem dvd_m_mul_coeff (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) :
    ∀ e m n : ℕ, p ^ e ∣ n → (p : Polynomial ℤ) ^ e ∣ (m : Polynomial ℤ) * (F ^ n).coeff m := by
  intro e
  induction e with
  | zero => intro m n _; simp
  | succ e ih =>
    intro m n hn
    obtain ⟨k, rfl⟩ : p ∣ n := (dvd_pow_self p (by omega)).trans hn
    have hk : p ^ e ∣ k := by
      rw [pow_succ, mul_comm] at hn; exact Nat.dvd_of_mul_dvd_mul_left hp.pos hn
    have hc := coeff_dvd_of_dvd p (e + 1) _ (frob_pow_congr p hp F e k hk) m
    rw [coeff_sub, coeff_frobLift_pow p hp] at hc
    by_cases hm : p ∣ m
    · simp only [hm, ↓reduceIte] at hc
      obtain ⟨m', rfl⟩ := hm
      rw [Nat.mul_div_cancel_left _ hp.pos] at hc
      have h2 : (p : Polynomial ℤ) ^ (e + 1) ∣
          ((p * m' : ℕ) : Polynomial ℤ) * expand ℤ p ((F ^ k).coeff m') := by
        have := expand_dvd_of_dvd p e _ (ih m' k hk)
        rw [map_mul, map_natCast] at this
        rw [pow_succ, Nat.cast_mul, mul_assoc, mul_comm ((p : Polynomial ℤ) ^ e)]
        exact mul_dvd_mul_left _ this
      have e1 : ((p * m' : ℕ) : Polynomial ℤ) * (F ^ (p * k)).coeff (p * m') =
          ((p * m' : ℕ) : Polynomial ℤ) *
            ((F ^ (p * k)).coeff (p * m') - expand ℤ p ((F ^ k).coeff m')) +
          ((p * m' : ℕ) : Polynomial ℤ) * expand ℤ p ((F ^ k).coeff m') := by ring
      rw [e1]
      exact dvd_add (dvd_mul_of_dvd_right hc _) h2
    · simp only [hm, ↓reduceIte, sub_zero] at hc
      exact dvd_mul_of_dvd_right hc _

/-- `p^e ∣ n ⇒ p^(e+1) ∣ [x^(p m)] F^(p n) - expand p ([x^m] F^n)`. -/
theorem coeff_frob_congr (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) (e m n : ℕ)
    (hn : p ^ e ∣ n) :
    (p : Polynomial ℤ) ^ (e + 1) ∣ (F ^ (p * n)).coeff (p * m) - expand ℤ p ((F ^ n).coeff m) := by
  have hc := coeff_dvd_of_dvd p (e + 1) _ (frob_pow_congr p hp F e n hn) (p * m)
  rw [coeff_sub, coeff_frobLift_pow p hp] at hc
  simp only [dvd_mul_right p m, ↓reduceIte] at hc
  rwa [Nat.mul_div_cancel_left _ hp.pos] at hc

/-! ## The integer array `V m n = m [x^m] F^n (y n) / n` -/

/-- Admissible evaluation points: `p^e ∣ n ⇒ p^(e+1) ∣ y (p n) ^ p - y n` for every prime. -/
def YCond (y : ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e n : ℕ, p ^ e ∣ n → (p : ℤ) ^ (e + 1) ∣ y (p * n) ^ p - y n

theorem ycond_zero : YCond (fun _ => 0) := by
  intro p hp e n _
  simp [zero_pow hp.ne_zero]

theorem ycond_pow (q : ℤ) : YCond (fun n => q ^ n) := by
  intro p hp e n hn
  obtain ⟨t, rfl⟩ := hn
  simp only
  have h1 := pow_gauss p hp q (e + 2) t (by omega)
  have h2 := pow_gauss p hp q (e + 1) t (by omega)
  have e1 : (q ^ (p * (p ^ e * t))) ^ p = q ^ (t * p ^ (e + 2)) := by
    rw [← pow_mul]; congr 1; ring
  have e2 : q ^ (p ^ e * t) = q ^ (t * p ^ (e + 1 - 1)) := by
    congr 1; rw [show e + 1 - 1 = e by omega]; ring
  rw [e1, e2]
  have e3 : q ^ (t * p ^ (e + 2)) - q ^ (t * p ^ (e + 1 - 1)) =
      (q ^ (t * p ^ (e + 2)) - q ^ (t * p ^ (e + 2 - 1))) +
      (q ^ (t * p ^ (e + 1)) - q ^ (t * p ^ (e + 1 - 1))) := by
    rw [show e + 2 - 1 = e + 1 by omega]; ring
  rw [e3]
  exact dvd_add ((pow_dvd_pow _ (by omega)).trans h1) h2

/-- `V F y m n = m * ([x^m] F^n)(y n) / n` (exact, `V_mul`). -/
noncomputable def V (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (m n : ℕ) : ℤ :=
  ((m : ℤ) * ((F ^ n).coeff m).eval (y n)) / n

theorem V_mul (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (m n : ℕ) :
    (n : ℤ) * V F y m n = (m : ℤ) * ((F ^ n).coeff m).eval (y n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [coeff_one, hm.ne']
  · unfold V
    apply Int.mul_ediv_cancel'
    apply dvd_of_prime_pows n hn.ne'
    intro p hp
    have := dvd_m_mul_coeff p hp F (n.factorization p) m n (Nat.ordProj_dvd n p)
    have := eval_dvd_of_dvd p _ _ this (y n)
    simpa [eval_mul] using this

theorem cancel_vp (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : n ≠ 0) (r : ℕ) (X : ℤ)
    (h : (p : ℤ) ^ (n.factorization p + r) ∣ (n : ℤ) * X) : (p : ℤ) ^ r ∣ X := by
  have hn'' : n = p ^ n.factorization p * (n / p ^ n.factorization p) :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hn' : (n : ℤ) = (p : ℤ) ^ n.factorization p * ((n / p ^ n.factorization p : ℕ) : ℤ) := by
    conv_lhs => rw [hn'']
    push_cast; ring
  rw [hn', pow_add, mul_assoc] at h
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))).mp h
  have hcop : IsCoprime ((p : ℤ) ^ r) ((n / p ^ n.factorization p : ℕ) : ℤ) := by
    apply IsCoprime.pow_left
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_ordCompl hp hn))).symm
  exact hcop.dvd_of_dvd_mul_left h2

theorem fact_le_of_not_dvd (p n s : ℕ)
    (h : ¬ p ^ (s + 1) ∣ n) : n.factorization p ≤ s := by
  by_contra hc
  exact h ((pow_dvd_pow p (by omega)).trans (Nat.ordProj_dvd n p))

theorem V0 (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (k s m n : ℕ)
    (hm : p ^ k ∣ m) (hn : ¬ p ^ (s + 1) ∣ n) : (p : ℤ) ^ (k - s) ∣ V F y m n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hs := fact_le_of_not_dvd p n s hn
  apply cancel_vp p hp n hn0
  rw [V_mul]
  rcases le_or_gt s k with hks | hks
  · apply dvd_mul_of_dvd_left
    have hm' : (p : ℤ) ^ k ∣ (m : ℤ) := by exact_mod_cast hm
    exact (pow_dvd_pow _ (by omega)).trans hm'
  · rw [show k - s = 0 by omega, add_zero]
    have := dvd_m_mul_coeff p hp F (n.factorization p) m n (Nat.ordProj_dvd n p)
    have := eval_dvd_of_dvd p _ _ this (y n)
    simpa [eval_mul] using this

theorem V1 (p : ℕ) (hp : p.Prime) (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (hy : YCond y)
    (k m n : ℕ) (hm : p ^ k ∣ m) : (p : ℤ) ^ (k + 1) ∣ V F y (p * m) (p * n) - V F y m n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [V]
  have hn0 : n ≠ 0 := hn.ne'
  apply cancel_vp p hp n hn0
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e1 : (n : ℤ) * (V F y (p * m) (p * n) - V F y m n) =
      (m : ℤ) * (((F ^ (p * n)).coeff (p * m)).eval (y (p * n)) -
        ((F ^ n).coeff m).eval (y n)) := by
    have a1 := V_mul F y (p * m) (p * n)
    have a2 := V_mul F y m n
    push_cast at a1
    apply mul_left_cancel₀ hp0
    linear_combination a1 - (p : ℤ) * a2
  rw [e1]
  set e := n.factorization p
  have hD : (p : ℤ) ^ (e + 1) ∣ ((F ^ (p * n)).coeff (p * m)).eval (y (p * n)) -
      ((F ^ n).coeff m).eval (y n) := by
    have h1 := eval_dvd_of_dvd p _ _ (coeff_frob_congr p hp F e m n (Nat.ordProj_dvd n p))
      (y (p * n))
    rw [eval_sub, expand_eval] at h1
    have h2 := (hy p hp e n (Nat.ordProj_dvd n p)).trans
      (sub_dvd_eval_sub (y (p * n) ^ p) (y n) ((F ^ n).coeff m))
    have e2 : ((F ^ (p * n)).coeff (p * m)).eval (y (p * n)) - ((F ^ n).coeff m).eval (y n) =
        (((F ^ (p * n)).coeff (p * m)).eval (y (p * n)) -
          ((F ^ n).coeff m).eval (y (p * n) ^ p)) +
        (((F ^ n).coeff m).eval (y (p * n) ^ p) - ((F ^ n).coeff m).eval (y n)) := by ring
    rw [e2]; exact dvd_add h1 h2
  rw [show e + (k + 1) = k + (e + 1) by ring, pow_add]
  have hm' : (p : ℤ) ^ k ∣ (m : ℤ) := by exact_mod_cast hm
  exact mul_dvd_mul hm' hD

/-! ## Weights and the row sums -/

/-- Weight condition at `p`: Gauss congruences along every ray. -/
def W1 (p : ℕ) (W : ℕ → ℕ → ℤ) : Prop :=
  ∀ k m n, p ^ k ∣ m → p ^ k ∣ n → (p : ℤ) ^ (k + 1) ∣ W (p * m) (p * n) - W m n

theorem W1_one (p : ℕ) : W1 p (fun _ _ => 1) := by
  intro k m n _ _; simp

/-- `W m n = u n ^ κ m n` with `u` a Gauss sequence, `κ (p m) (p n) = p κ m n` and
`p^k ∣ m, n ⇒ p^k ∣ κ m n`. -/
theorem W1_pow (p : ℕ) (hp : p.Prime) (u : ℕ → ℤ) (hu : LGp p u) (κ : ℕ → ℕ → ℕ)
    (hκ1 : ∀ m n, κ (p * m) (p * n) = p * κ m n)
    (hκ2 : ∀ k m n, p ^ k ∣ m → p ^ k ∣ n → p ^ k ∣ κ m n) :
    W1 p (fun m n => u n ^ κ m n) := by
  intro k m n hm hn
  simp only
  obtain ⟨t, ht⟩ := hκ2 k m n hm hn
  obtain ⟨n', rfl⟩ := hn
  rw [hκ1, ht]
  have h1 : (p : ℤ) ^ (k + 1) ∣ u (p * (p ^ k * n')) - u (p ^ k * n') := by
    have := hu (k + 1) n' (by omega)
    rwa [show n' * p ^ (k + 1) = p * (p ^ k * n') by ring,
      show n' * p ^ (k + 1 - 1) = p ^ k * n' by rw [show k + 1 - 1 = k by omega]; ring] at this
  have h2 := pow_gauss p hp (u (p ^ k * n')) (k + 1) t (by omega)
  have e : u (p * (p ^ k * n')) ^ (p * (p ^ k * t)) - u (p ^ k * n') ^ (p ^ k * t) =
      (u (p * (p ^ k * n')) ^ (p * (p ^ k * t)) - u (p ^ k * n') ^ (p * (p ^ k * t))) +
      (u (p ^ k * n') ^ (t * p ^ (k + 1)) - u (p ^ k * n') ^ (t * p ^ (k + 1 - 1))) := by
    rw [show k + 1 - 1 = k by omega, show t * p ^ (k + 1) = p * (p ^ k * t) by ring,
      show t * p ^ k = p ^ k * t by ring]; ring
  rw [e]
  exact dvd_add (h1.trans (sub_dvd_pow_sub_pow _ _ _)) h2

/-- Row sums of an array with the two ray congruences are Gauss sequences. -/
theorem rowsum_gauss (p : ℕ) (hp : p.Prime) (T : ℕ → ℕ → ℤ)
    (hT0 : ∀ k m n, p ^ k ∣ m → ¬ p ∣ n → (p : ℤ) ^ k ∣ T m n)
    (hT1 : ∀ k m n, p ^ k ∣ m → (p : ℤ) ^ (k + 1) ∣ T (p * m) (p * n) - T m n) :
    LGp p (fun m => ∑ n ∈ Finset.range (m + 1), T m n) := by
  intro a m0 ha
  simp only
  set M := m0 * p ^ (a - 1)
  have hN : m0 * p ^ a = p * M := by
    simp only [M]; rw [← mul_assoc, mul_comm p m0, mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
  rw [hN, ← Finset.sum_filter_add_sum_filter_not (Finset.range (p * M + 1)) (fun n => p ∣ n)]
  have himg : (Finset.range (p * M + 1)).filter (fun n => p ∣ n) =
      (Finset.range (M + 1)).image (fun n => p * n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, ⟨t, rfl⟩⟩
      exact ⟨t, by
        by_contra h
        have h := Nat.le_of_not_lt h
        have : p * (M + 1) ≤ p * t := Nat.mul_le_mul_left p h
        nlinarith [hp.pos], rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by nlinarith [hp.pos], dvd_mul_right _ _⟩
  rw [himg, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
  have e : ∑ x ∈ Finset.range (M + 1), T (p * M) (p * x) +
      ∑ n ∈ (Finset.range (p * M + 1)).filter (fun n => ¬ p ∣ n), T (p * M) n -
      ∑ n ∈ Finset.range (M + 1), T M n =
      ∑ x ∈ Finset.range (M + 1), (T (p * M) (p * x) - T M x) +
      ∑ n ∈ (Finset.range (p * M + 1)).filter (fun n => ¬ p ∣ n), T (p * M) n := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  have hM : p ^ (a - 1) ∣ M := Dvd.intro_left _ rfl
  apply dvd_add
  · apply Finset.dvd_sum
    intro x _
    have := hT1 (a - 1) M x hM
    rwa [show a - 1 + 1 = a by omega] at this
  · apply Finset.dvd_sum
    intro n hn
    rw [Finset.mem_filter] at hn
    apply hT0 a (p * M) n _ hn.2
    rw [← hN]; exact Dvd.intro_left _ rfl

/-- `rowB F y W m = ∑_{n ≤ m} W m n * V F y m n`: the `x`-log-derivative coefficients of
`exp (Φ (log (1 / (1 - y F))))` for `Φ : x^m y^n ↦ W m n x^m`. -/
noncomputable def rowB (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (W : ℕ → ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (m + 1), W m n * V F y m n

theorem rowB_gauss (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (hy : YCond y)
    (W : ℕ → ℕ → ℤ) (p : ℕ) (hp : p.Prime) (hW : W1 p W) : LGp p (rowB F y W) := by
  apply rowsum_gauss p hp (fun m n => W m n * V F y m n)
  · intro k m n hm hn
    apply dvd_mul_of_dvd_right
    have := V0 p hp F y k 0 m n hm (by simpa using hn)
    simpa using this
  · intro k m n hm
    have hV1 := V1 p hp F y hy k m n hm
    have e : W (p * m) (p * n) * V F y (p * m) (p * n) - W m n * V F y m n =
        W (p * m) (p * n) * (V F y (p * m) (p * n) - V F y m n) +
        V F y m n * (W (p * m) (p * n) - W m n) := by ring
    rw [e]
    apply dvd_add (dvd_mul_of_dvd_right hV1 _)
    by_cases hkn : p ^ k ∣ n
    · exact dvd_mul_of_dvd_right (hW k m n hm hkn) _
    · have hn0 : n ≠ 0 := by rintro rfl; exact hkn (dvd_zero _)
      set t := n.factorization p
      have htk : t < k := by
        by_contra h
        have h := Nat.le_of_not_lt h
        exact hkn ((pow_dvd_pow p h).trans (Nat.ordProj_dvd n p))
      have hVt := V0 p hp F y k t m n hm (Nat.pow_succ_factorization_not_dvd hn0 hp)
      have hWt := hW t m n ((pow_dvd_pow p htk.le).trans hm) (Nat.ordProj_dvd n p)
      rw [show k + 1 = (k - t) + (t + 1) by omega, pow_add]
      exact mul_dvd_mul hVt hWt

/-- The bivariate Euler-product lemma (coefficient form): if the evaluation points are admissible
and the weights satisfy the ray Gauss congruences at every prime, then
`exp (∑_m rowB F y W m x^m / m)` has integer coefficients. -/
theorem rowB_int (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (hy : YCond y)
    (W : ℕ → ℕ → ℤ) (hW : ∀ p : ℕ, p.Prime → W1 p W) (N : ℕ) :
    ∃ z : ℤ, expCoeff (rowB F y W) N = z :=
  expCoeff_int_of_gauss _ (fun p hp => rowB_gauss F y hy W p hp (hW p hp)) N

/-! ## Gluing an OEIS functional equation to `rowB`

`recSeq bf` is the coefficient sequence `a` of `exp (S)` where `x S'` has coefficients
`bf a m` that may themselves depend on `a 0, ..., a (m-1)` (functional equations such as
`A(x) = exp(∑ A(L(n) x)^n x^n / n)`): `a 0 = 1` and
`(N+1) a (N+1) = ∑_{j ≤ N} bf a (j+1) a (N-j)`. -/

/-- `recUpTo bf N i = a i` for `i ≤ N` (primitive recursion on `N`). -/
def recUpTo (bf : (ℕ → ℚ) → ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => fun _ => 1
  | N + 1 => fun i => if i ≤ N then recUpTo bf N i else
      (∑ j ∈ Finset.range (N + 1), bf (recUpTo bf N) (j + 1) * recUpTo bf N (N - j)) / (N + 1)

/-- The sequence defined by `a 0 = 1`, `(N+1) a (N+1) = ∑_{j ≤ N} bf a (j+1) a (N-j)`. -/
def recSeq (bf : (ℕ → ℚ) → ℕ → ℚ) (N : ℕ) : ℚ := recUpTo bf N N

theorem recUpTo_stable (bf : (ℕ → ℚ) → ℕ → ℚ) (i : ℕ) :
    ∀ N, i ≤ N → recUpTo bf N i = recSeq bf i := by
  intro N
  induction N with
  | zero => intro h; rw [Nat.le_zero.mp h]; rfl
  | succ N ih =>
    intro h
    rcases Nat.lt_or_ge i (N + 1) with h1 | h1
    · simp only [recUpTo, show i ≤ N by omega, ↓reduceIte]; exact ih (by omega)
    · rw [show i = N + 1 by omega]; rfl

/-- `bf g m` only reads `g 0, ..., g (m-1)`. -/
def Local (bf : (ℕ → ℚ) → ℕ → ℚ) : Prop :=
  ∀ g g' m, (∀ i, i < m → g i = g' i) → bf g m = bf g' m

theorem recSeq_zero (bf : (ℕ → ℚ) → ℕ → ℚ) : recSeq bf 0 = 1 := rfl

theorem recSeq_rec (bf : (ℕ → ℚ) → ℕ → ℚ) (hloc : Local bf) (N : ℕ) :
    ((N : ℚ) + 1) * recSeq bf (N + 1) =
      ∑ j ∈ Finset.range (N + 1), bf (recSeq bf) (j + 1) * recSeq bf (N - j) := by
  have h : recSeq bf (N + 1) =
      (∑ j ∈ Finset.range (N + 1), bf (recUpTo bf N) (j + 1) * recUpTo bf N (N - j)) / (N + 1) := by
    simp [recSeq, recUpTo]
  rw [h, mul_div_cancel₀ _ (by positivity)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [recUpTo_stable bf (N - j) N (by omega)]
  congr 1
  exact hloc _ _ _ (fun i hi => recUpTo_stable bf i N (by omega))

/-- Integrality of `recSeq bf`: it suffices that for every integer sequence `gz` and every `N`,
the values `bf gz m` (`1 ≤ m ≤ N`) are the terms of an integer Gauss sequence. -/
theorem recSeq_int (bf : (ℕ → ℚ) → ℕ → ℚ) (hloc : Local bf)
    (hint : ∀ (gz : ℕ → ℤ) (N : ℕ), ∃ b : ℕ → ℤ, (∀ p : ℕ, p.Prime → LGp p b) ∧
      ∀ m, 1 ≤ m → m ≤ N → bf (fun i => (gz i : ℚ)) m = b m) :
    ∀ N, ∃ z : ℤ, recSeq bf N = z := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    set gz : ℕ → ℤ := fun i => ⌊recSeq bf i⌋
    have hgz : ∀ i, i < N → (gz i : ℚ) = recSeq bf i := by
      intro i hi
      obtain ⟨z, hz⟩ := ih i hi
      simp [gz, hz]
    obtain ⟨b, hb, hbeq⟩ := hint gz N
    refine ⟨_, eq_expCoeff_of_rec b (recSeq bf) N (recSeq_zero bf) ?_ N le_rfl |>.trans
      (expCoeff_int_of_gauss b hb N).choose_spec⟩
    intro n hn
    rw [recSeq_rec bf hloc n]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← hbeq (j + 1) (by omega) (by omega)]
    congr 1
    exact hloc _ _ _ (fun i hi => (hgz i (by omega)).symm)

/-! ## Polynomial helpers for the glue -/

/-- `g 0 + g 1 x + ... + g (N-1) x^(N-1)`. -/
noncomputable def gpoly {R : Type*} [CommRing R] (g : ℕ → R) (N : ℕ) : R[X] :=
  ∑ i ∈ Finset.range N, C (g i) * X ^ i

theorem coeff_gpoly {R : Type*} [CommRing R] (g : ℕ → R) (N i : ℕ) :
    (gpoly g N).coeff i = if i < N then g i else 0 := by
  simp only [gpoly, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases h : i < N
  · rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp [h])]; simp [h]
  · rw [Finset.sum_eq_zero (fun b hb => by
      rw [Finset.mem_range] at hb; simp [show i ≠ b by omega])]; simp [h]

theorem map_gpoly (g : ℕ → ℤ) (N : ℕ) :
    (gpoly g N).map (Int.castRingHom ℚ) = gpoly (fun i => (g i : ℚ)) N := by
  simp [gpoly, Polynomial.map_sum]

/-- Scaling: `[x^i] f(c x) = c^i [x^i] f`. -/
theorem coeff_comp_C_mul_X {R : Type*} [CommRing R] (f : R[X]) (c : R) (i : ℕ) :
    (f.comp (C c * X)).coeff i = c ^ i * f.coeff i := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [add_comp, hf, hg, mul_add]
  | monomial k a =>
    rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : i = k
    · subst h; simp; ring
    · simp [h, Ne.symm h]

/-- `[x^m] (x f)^n` only reads `f` below degree `m`. -/
theorem coeff_X_mul_pow_congr {R : Type*} [CommRing R] (f f' : R[X]) (m n : ℕ)
    (h : ∀ i, i < m → f.coeff i = f'.coeff i) :
    ((X * f) ^ n).coeff m = ((X * f') ^ n).coeff m := by
  have h1 : X ^ m ∣ f - f' := X_pow_dvd_iff.mpr (fun d hd => by simp [h d hd])
  have h2 : X ^ (m + 1) ∣ (X * f) ^ n - (X * f') ^ n := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ n)
    rw [← mul_sub, pow_succ']
    exact mul_dvd_mul_left X h1
  have := (X_pow_dvd_iff.mp h2) m (by omega)
  rw [coeff_sub] at this
  exact sub_eq_zero.mp this

/-- For `F` constant in `Y`, `V` is `m / n * [x^m] f^n`. -/
theorem V_cast_map (f : Polynomial ℤ) (y : ℕ → ℤ) (m n : ℕ) :
    (V (f.map C) y m n : ℚ) = (m : ℚ) / n * (((f ^ n).coeff m : ℤ) : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [V]
  · have h := V_mul (f.map C) y m n
    rw [← Polynomial.map_pow, coeff_map, eval_C] at h
    have hn' : (n : ℚ) ≠ 0 := by positivity
    field_simp
    rw [mul_comm] at h
    exact_mod_cast h

/-- `V` with an evaluation point: `m / n * [x^m] (F evaluated at Y = y n)^n`. -/
theorem V_cast_eval (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (m n : ℕ) :
    (V F y m n : ℚ) =
      (m : ℚ) / n * ((((F.map (evalRingHom (y n))) ^ n).coeff m : ℤ) : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [V]
  · have h := V_mul F y m n
    rw [← Polynomial.map_pow, coeff_map, coe_evalRingHom] at *
    have hn' : (n : ℚ) ≠ 0 := by positivity
    field_simp
    rw [mul_comm] at h
    exact_mod_cast h

theorem range_succ_eq_insert_Icc (m : ℕ) :
    Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
  ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega

/-- `rowB` as a sum over `1 ≤ n ≤ m`. -/
theorem rowB_eq_Icc (F : Polynomial (Polynomial ℤ)) (y : ℕ → ℤ) (W : ℕ → ℕ → ℤ) (m : ℕ) :
    rowB F y W m = ∑ n ∈ Finset.Icc 1 m, W m n * V F y m n := by
  rw [rowB, range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
  simp [V]

/-- `[x^m] (x G_N)^n = [x^(m-n)] G_m^n` for the integer truncation `G_N = ∑_{i<N} gz i x^i`,
`n ≤ m ≤ N` (cast to `ℚ`). -/
theorem coeff_X_mul_gpoly_pow (gz : ℕ → ℤ) (N m n : ℕ) (hm : m ≤ N) (hn : n ≤ m) :
    ((((X * gpoly gz N) ^ n).coeff m : ℤ) : ℚ) =
      ((gpoly (fun i => (gz i : ℚ)) m) ^ n).coeff (m - n) := by
  have h1 : ((((X * gpoly gz N) ^ n).coeff m : ℤ) : ℚ) =
      ((X * gpoly (fun i => (gz i : ℚ)) N) ^ n).coeff m := by
    rw [← map_gpoly, ← Polynomial.map_X (Int.castRingHom ℚ), ← Polynomial.map_mul,
      ← Polynomial.map_pow, coeff_map, eq_intCast]
  rw [h1, coeff_X_mul_pow_congr _ (gpoly (fun i => (gz i : ℚ)) m) m n (fun i hi => by
      rw [coeff_gpoly, coeff_gpoly]; simp [hi, show i < N by omega]),
    mul_pow, coeff_X_pow_mul']
  simp only [hn, ↓reduceIte]

/-! ## Power families: `T m n = (m / n) U(m,n)^(G(m,n) + 1)` with `U(m,n) = [x^m] (x f)^n`

Used for `exp (∑_n (∑_k B(n,k)^e(n,k) x^k) x^n / n)` with `B(n,k) = [x^(n+k)] (x f)^n`
(`f = 1 + x`: `C(n,k)`; `f = 1 + x + ... `: `C(n+k-1,k)`), `G = e - 1`. -/

theorem euler_lift (p : ℕ) (hp : p.Prime) (x : ℤ) (hx : ¬ (p : ℤ) ∣ x) (t : ℕ) :
    (p : ℤ) ^ (t + 1) ∣ x ^ ((p - 1) * p ^ t) - 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : (p : ℤ) ∣ x ^ (p - 1) - 1 := by
    have h := fermat_int p hp x
    have e : x ^ p - x = x * (x ^ (p - 1) - 1) := by
      rw [mul_sub, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le]; ring
    rw [e] at h
    exact (hpz.dvd_or_dvd h).resolve_left hx
  have := dvd_sub_pow_of_dvd_sub (by simpa using h1) t
  rwa [one_pow, ← pow_mul] at this

/-- The integer `U m n = [x^m] (x f)^n`. -/
noncomputable def U (f : Polynomial ℤ) (m n : ℕ) : ℤ := ((X * f) ^ n).coeff m

theorem U_eq_eval (f : Polynomial ℤ) (m n : ℕ) :
    ((((X * f).map C) ^ n).coeff m).eval 0 = U f m n := by
  rw [← Polynomial.map_pow, coeff_map, eval_C, U]

theorem V_mul_U (f : Polynomial ℤ) (m n : ℕ) :
    (n : ℤ) * V ((X * f).map C) (fun _ => 0) m n = m * U f m n := by
  rw [V_mul, U_eq_eval]

theorem U_zero_of_lt (f : Polynomial ℤ) (m n : ℕ) (h : m < n) : U f m n = 0 := by
  rw [U, mul_pow, coeff_X_pow_mul']; simp [show ¬ n ≤ m by omega]

theorem U_congr (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) (e m n : ℕ) (hn : p ^ e ∣ n) :
    (p : ℤ) ^ (e + 1) ∣ U f (p * m) (p * n) - U f m n := by
  have h := eval_dvd_of_dvd p _ _ (coeff_frob_congr p hp ((X * f).map C) e m n hn) 0
  rwa [eval_sub, expand_eval, zero_pow hp.ne_zero, U_eq_eval, U_eq_eval] at h

/-- The array of a power family. -/
noncomputable def Tpow (f : Polynomial ℤ) (G : ℕ → ℕ → ℕ) (m n : ℕ) : ℤ :=
  V ((X * f).map C) (fun _ => 0) m n * U f m n ^ G m n

/-- Conditions on the exponent `G` at the prime `p` (for `1 ≤ n ≤ m`). -/
structure GCond (p : ℕ) (f : Polynomial ℤ) (G : ℕ → ℕ → ℕ) : Prop where
  mono : ∀ m n, 1 ≤ n → n ≤ m → G m n ≤ G (p * m) (p * n)
  euler : ∀ m n t, 1 ≤ n → n ≤ m → p ^ t ∣ m → p ^ t ∣ n →
    (p - 1) * p ^ t ∣ G (p * m) (p * n) - G m n
  big : ∀ m n, 1 ≤ n → n ≤ m → (p : ℤ) ∣ U f m n → U f m n ≠ 0 →
    min (n.factorization p) (m.factorization p + 1) ≤ G m n

theorem second_term (p : ℕ) (hp : p.Prime) (k s mv : ℕ) (V0 U' U0 : ℤ) (G' G0 : ℕ)
    (hGle : G0 ≤ G') (hks : k ≤ mv)
    (hcong : ∀ t, t ≤ k → t ≤ s → (p : ℤ) ^ (t + 1) ∣ U' - U0)
    (heul : ∀ t, t ≤ k → t ≤ s → (p - 1) * p ^ t ∣ G' - G0)
    (hbig : (p : ℤ) ∣ U0 → U0 ≠ 0 → min s (mv + 1) ≤ G0)
    (hz : U0 = 0 → V0 = 0)
    (hVa : (p : ℤ) ^ (k - s) ∣ V0)
    (hVb : (p : ℤ) ∣ U0 → (p : ℤ) ^ (k + 1 - s) ∣ V0) :
    (p : ℤ) ^ (k + 1) ∣ V0 * (U' ^ G' - U0 ^ G0) := by
  by_cases hU : (p : ℤ) ∣ U0
  · by_cases hU0 : U0 = 0
    · rw [hz hU0, zero_mul]; exact dvd_zero _
    have hb := hbig hU hU0
    have hU' : (p : ℤ) ∣ U' := by
      have h := hcong 0 (Nat.zero_le _) (Nat.zero_le _)
      rw [zero_add, pow_one] at h
      have h2 := dvd_add h hU
      simpa using h2
    have hW : (p : ℤ) ^ G0 ∣ U' ^ G' - U0 ^ G0 :=
      dvd_sub ((pow_dvd_pow _ hGle).trans (pow_dvd_pow_of_dvd hU' _)) (pow_dvd_pow_of_dvd hU _)
    by_cases hs : s ≤ k
    · have h1 : k + 1 ≤ (k + 1 - s) + G0 := by omega
      exact (pow_dvd_pow _ h1).trans (by rw [pow_add]; exact mul_dvd_mul (hVb hU) hW)
    · have h1 : k + 1 ≤ G0 := by omega
      exact dvd_mul_of_dvd_right ((pow_dvd_pow _ h1).trans hW) _
  · have h1 := hcong (min k s) (min_le_left _ _) (min_le_right _ _)
    obtain ⟨d, hd⟩ := heul (min k s) (min_le_left _ _) (min_le_right _ _)
    have h2 : (p : ℤ) ^ (min k s + 1) ∣ U0 ^ (G' - G0) - 1 := by
      rw [hd, pow_mul]
      exact (euler_lift p hp U0 hU _).trans (by simpa using sub_dvd_pow_sub_pow _ (1 : ℤ) d)
    have hW : (p : ℤ) ^ (min k s + 1) ∣ U' ^ G' - U0 ^ G0 := by
      have e2 : U' ^ G' - U0 ^ G0 = (U' ^ G' - U0 ^ G') + U0 ^ G0 * (U0 ^ (G' - G0) - 1) := by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hGle]; ring
      rw [e2]
      exact dvd_add (h1.trans (sub_dvd_pow_sub_pow _ _ _)) (dvd_mul_of_dvd_right h2 _)
    have hV : (p : ℤ) ^ (k - min k s) ∣ V0 := (pow_dvd_pow _ (by omega)).trans hVa
    rw [show k + 1 = (k - min k s) + (min k s + 1) by omega, pow_add]
    exact mul_dvd_mul hV hW

-- The final `refine` unifies two large `V`/`U` terms; the default budget is too small.
set_option maxHeartbeats 1000000 in
theorem Tpow_T1 (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) (G : ℕ → ℕ → ℕ) (hG : GCond p f G)
    (k m n : ℕ) (hm : p ^ k ∣ m) :
    (p : ℤ) ^ (k + 1) ∣ Tpow f G (p * m) (p * n) - Tpow f G m n := by
  have hp0 : 0 < p := hp.pos
  have hV0 : ∀ m n, U f m n = 0 → V ((X * f).map C) (fun _ => 0) m n = 0 := by
    intro m n h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [V]
    · have := V_mul_U f m n
      rw [h, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hn.ne')
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have z : ∀ m', Tpow f G m' 0 = 0 := fun m' => by
      have : V ((X * f).map C) (fun _ => 0) m' 0 = 0 := by unfold V; rw [Nat.cast_zero, Int.ediv_zero]
      unfold Tpow; rw [this, zero_mul]
    rw [mul_zero, z, z, sub_zero]; exact dvd_zero _
  rcases Nat.lt_or_ge m n with hmn | hmn
  · have h1 := U_zero_of_lt f m n hmn
    have h2 := U_zero_of_lt f (p * m) (p * n) (Nat.mul_lt_mul_of_pos_left hmn hp0)
    have z1 : Tpow f G m n = 0 := by unfold Tpow; rw [hV0 m n h1, zero_mul]
    have z2 : Tpow f G (p * m) (p * n) = 0 := by unfold Tpow; rw [hV0 _ _ h2, zero_mul]
    rw [z1, z2, sub_zero]; exact dvd_zero _
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have e : Tpow f G (p * m) (p * n) - Tpow f G m n =
      U f (p * m) (p * n) ^ G (p * m) (p * n) *
        (V ((X * f).map C) (fun _ => 0) (p * m) (p * n) - V ((X * f).map C) (fun _ => 0) m n) +
      V ((X * f).map C) (fun _ => 0) m n *
        (U f (p * m) (p * n) ^ G (p * m) (p * n) - U f m n ^ G m n) := by
    unfold Tpow; ring
  rw [e]
  refine dvd_add (dvd_mul_of_dvd_right ?_ _) ?_
  · exact V1 p hp ((X * f).map C) (fun _ => 0) ycond_zero k m n hm
  have hkm : k ≤ m.factorization p := (hp.pow_dvd_iff_le_factorization hm0).mp hm
  refine second_term p hp k (n.factorization p) (m.factorization p)
    (V ((X * f).map C) (fun _ => 0) m n) (U f (p * m) (p * n)) (U f m n)
    (G (p * m) (p * n)) (G m n) (hG.mono m n hn1 hmn) hkm ?_ ?_ ?_ ?_ ?_ ?_
  · intro t htk hts
    exact U_congr p hp f t m n ((pow_dvd_pow p hts).trans (Nat.ordProj_dvd n p))
  · intro t htk hts
    exact hG.euler m n t hn1 hmn ((pow_dvd_pow p htk).trans hm)
      ((pow_dvd_pow p hts).trans (Nat.ordProj_dvd n p))
  · exact hG.big m n hn1 hmn
  · exact hV0 m n
  · exact V0 p hp ((X * f).map C) (fun _ => 0) k (n.factorization p) m n hm
      (Nat.pow_succ_factorization_not_dvd hn0 hp)
  · intro hU
    by_cases hs : n.factorization p ≤ k + 1
    · apply cancel_vp p hp n hn0
      rw [V_mul_U, show n.factorization p + (k + 1 - n.factorization p) = k + 1 by omega,
        pow_succ]
      have hm' : (p : ℤ) ^ k ∣ (m : ℤ) := by exact_mod_cast hm
      exact mul_dvd_mul hm' hU
    · rw [show k + 1 - n.factorization p = 0 by omega, pow_zero]; exact one_dvd _

/-- Power families have Gauss row sums. -/
theorem Tpow_gauss (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) (G : ℕ → ℕ → ℕ)
    (hG : GCond p f G) : LGp p (fun m => ∑ n ∈ Finset.range (m + 1), Tpow f G m n) := by
  apply rowsum_gauss p hp _ _ (Tpow_T1 p hp f G hG)
  intro k m n hm hn
  apply dvd_mul_of_dvd_left
  have := V0 p hp ((X * f).map C) (fun _ => 0) k 0 m n hm (by simpa using hn)
  simpa using this

/-- `(Tpow f G m n : ℚ) = m / n * U^(G+1)`. -/
theorem Tpow_cast (f : Polynomial ℤ) (G : ℕ → ℕ → ℕ) (m n : ℕ) :
    (Tpow f G m n : ℚ) = (m : ℚ) / n * (U f m n : ℚ) ^ (G m n + 1) := by
  rw [Tpow, Int.cast_mul, V_cast_map, ← U, Int.cast_pow, pow_succ]; ring

/-- Helper for `GCond.big`: a positive multiple `c ≤ G` of `p^min(v_p m, v_p n)`. -/
theorem big_of_dvd (p : ℕ) (hp : p.Prime) (m n c g : ℕ) (hc : 1 ≤ c)
    (hdvd : p ^ min (m.factorization p) (n.factorization p) ∣ c) (hcg : c ≤ g) :
    min (n.factorization p) (m.factorization p + 1) ≤ g := by
  have h1 := Nat.le_of_dvd (by omega) hdvd
  have h2 : min (m.factorization p) (n.factorization p) <
      p ^ min (m.factorization p) (n.factorization p) := Nat.lt_pow_self hp.one_lt
  omega

/-- Helper for `GCond.big`: `v_p n ≤ G`. -/
theorem big_of_vp (p n m g : ℕ) (h : n.factorization p ≤ g) :
    min (n.factorization p) (m.factorization p + 1) ≤ g := by omega

theorem vp_lt (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : n ≠ 0) : n.factorization p < n :=
  lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p))

/-- `U (1 + X) m n = C(n, m - n)`. -/
theorem U_one_add_X (m n : ℕ) (h : n ≤ m) : U (1 + X) m n = (n.choose (m - n) : ℤ) := by
  rw [U, mul_pow, coeff_X_pow_mul']
  simp only [h, ↓reduceIte]
  exact coeff_one_add_X_pow ℤ n (m - n)

/-- `1 + x + ... + x^N`. -/
noncomputable def geomTrunc (N : ℕ) : Polynomial ℤ := PowerSeries.trunc (N + 1) (PowerSeries.mk 1)

/-- `U (1 + x + ... + x^N) m n = C(m - 1, m - n)` (`= C(n + k - 1, k)`, `k = m - n`) for
`1 ≤ n ≤ m ≤ N`. -/
theorem U_geom (N m n : ℕ) (h1 : 1 ≤ n) (h : n ≤ m) (hm : m ≤ N) :
    U (geomTrunc N) m n = ((m - 1).choose (m - n) : ℤ) := by
  rw [U, mul_pow, coeff_X_pow_mul']
  simp only [h, ↓reduceIte]
  have e1 : ((geomTrunc N) ^ n).coeff (m - n) =
      PowerSeries.coeff (m - n) ((PowerSeries.mk 1 : PowerSeries ℤ) ^ n) := by
    rw [← Polynomial.coeff_coe, Polynomial.coe_pow, geomTrunc]
    have := PowerSeries.coeff_trunc (m - n) (N + 1)
      (((PowerSeries.trunc (N + 1) (PowerSeries.mk 1 : PowerSeries ℤ) : Polynomial ℤ) :
        PowerSeries ℤ) ^ n)
    rw [PowerSeries.trunc_trunc_pow, PowerSeries.coeff_trunc] at this
    simp only [show m - n < N + 1 by omega, ↓reduceIte] at this
    exact this.symm
  rw [e1]
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk]
  have e2 : d + (m - (d + 1)) = m - 1 := by omega
  rw [e2, ← Nat.choose_symm (show m - (d + 1) ≤ m - 1 by omega),
    show m - 1 - (m - (d + 1)) = d by omega]

theorem U_diag (f : Polynomial ℤ) (hf : f.coeff 0 = 1) (m : ℕ) : U f m m = 1 := by
  rw [U, mul_pow, coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self, coeff_zero_eq_eval_zero, eval_pow]
  rw [← coeff_zero_eq_eval_zero, hf, one_pow]

/-- `GCond` for `G m n = if n = m then 0 else g n (m - n)` (exponent `g n k = e(n,k) - 1` of
`B(n,k)^e(n,k)`; the diagonal `k = 0` has `B = 1`). -/
theorem gcond_of (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) (hf : f.coeff 0 = 1) (g : ℕ → ℕ → ℕ)
    (hL : ∀ n k, 1 ≤ n → 1 ≤ k → ∃ L, g (p * n) (p * k) = g n k + (p - 1) * L ∧
      ∀ t, p ^ t ∣ n → p ^ t ∣ k → p ^ t ∣ L)
    (hbig : ∀ n k, 1 ≤ n → 1 ≤ k → (p : ℤ) ∣ U f (n + k) n → U f (n + k) n ≠ 0 →
      min (n.factorization p) ((n + k).factorization p + 1) ≤ g n k) :
    GCond p f (fun m n => if n = m then 0 else g n (m - n)) := by
  have hp0 := hp.pos
  have hsub : ∀ m n, p * m - p * n = p * (m - n) := fun m n => (Nat.mul_sub p m n).symm
  refine ⟨?_, ?_, ?_⟩
  · intro m n h1 h2
    by_cases hnm : n = m
    · simp [hnm]
    · have hpn : p * n ≠ p * m := fun h => hnm (Nat.eq_of_mul_eq_mul_left hp0 h)
      simp only [hnm, hpn, ↓reduceIte, hsub]
      obtain ⟨L, hL1, _⟩ := hL n (m - n) h1 (by omega)
      omega
  · intro m n t h1 h2 htm htn
    by_cases hnm : n = m
    · simp [hnm]
    · have hpn : p * n ≠ p * m := fun h => hnm (Nat.eq_of_mul_eq_mul_left hp0 h)
      simp only [hnm, hpn, ↓reduceIte, hsub]
      obtain ⟨L, hL1, hL2⟩ := hL n (m - n) h1 (by omega)
      rw [hL1, Nat.add_sub_cancel_left]
      exact mul_dvd_mul_left _ (hL2 t htn (Nat.dvd_sub htm htn))
  · intro m n h1 h2 hU hU0
    by_cases hnm : n = m
    · subst hnm
      rw [U_diag f hf] at hU
      exact absurd (Int.eq_one_of_dvd_one (by positivity) hU) (by exact_mod_cast hp.one_lt.ne')
    · simp only [hnm, ↓reduceIte]
      have hm : m = n + (m - n) := by omega
      rw [hm] at hU hU0
      have := hbig n (m - n) h1 (by omega) hU hU0
      rwa [← hm] at this

end OpenProblemsLib.DworkEuler
