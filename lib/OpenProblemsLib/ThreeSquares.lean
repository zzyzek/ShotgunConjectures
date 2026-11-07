import Mathlib

/-!
# Legendre's three-square theorem

`n ∈ ℕ` is a sum of three squares iff `n` is not of the form `4^a (8b + 7)`.

Route (Dirichlet's proof, geometry of numbers in place of Gauss reduction).
1. Every positive definite integral ternary form of determinant 1 is a sum of three squares of
   integral linear forms (`sum_three_sq_of_det_one`). Minkowski's convex body theorem on the
   ellipsoid `{Q < 2}` (volume `(4π/3) · 2^{3/2} / √det > 8` for `det ≤ 2`) gives `Q(v) = 1`;
   applied again to `Q + B(v,·)²` (determinant 2) it gives `w ⊥ v` with `Q(w) = 1`; the third
   vector is the cross product `Av × Aw`, with `Q(Av × Aw) = det A · (Q v Q w - B(v,w)²) = 1`.
2. For `n ≡ 1, 2, 3, 5, 6 (mod 8)` Dirichlet's theorem gives a prime `p` with `d n - 1 = p`
   (`n ≡ 2 mod 4`) or `= 2p` (`n` odd) and `-d` a square modulo `d n - 1` (Jacobi reciprocity).
   With `t² ≡ -d` and `a = (t² + d)/(d n - 1)` the form `[[a, t, 1], [t, d n - 1, 0], [1, 0, n]]`
   has determinant 1 and represents `n` (`sum_three_sq_of_mod_eight`).
3. Multiples of 4 by descent; `4^a (8b+7)` excluded by squares mod 8 (`not_sum_three_sq`).

Main results.
* `exists_small` : Minkowski for a positive definite real ternary form of determinant `≤ 2`.
* `sum_three_sq_of_det_one` : unimodular positive definite ternary forms represent only sums of
  three squares.
* `sum_three_sq_of_mod_eight` : `n ≡ 1, 2, 3, 5, 6 (mod 8)` is a sum of three squares.
* `not_sum_three_sq` : `x² + y² + z² ≠ 4^a (8b + 7)`.
* `sum_three_sq_iff` : over `ℕ`, `(∃ x y z, x² + y² + z² = n) ↔ ¬ ∃ a b, n = 4^a (8b + 7)`.
* `sum_three_sq_iff_int` : over `ℤ`, the same with `0 ≤ n`.

Checked: everything above, axioms propext, Classical.choice, Quot.sound. Not covered: the
number of representations (Gauss's `r₃` class-number formula).
-/

namespace OpenProblemsLib.ThreeSquares

open MeasureTheory Matrix

/-- The ternary quadratic form with Gram matrix `[[a,b,c],[b,d,e],[c,e,g]]`. -/
def qf {R : Type*} [CommRing R] (a b c d e g : R) (x : Fin 3 → R) : R :=
  a * x 0 ^ 2 + d * x 1 ^ 2 + g * x 2 ^ 2 + 2 * b * x 0 * x 1 + 2 * c * x 0 * x 2
    + 2 * e * x 1 * x 2

/-- The determinant of `[[a,b,c],[b,d,e],[c,e,g]]`. -/
def det3 {R : Type*} [CommRing R] (a b c d e g : R) : R :=
  a * (d * g - e ^ 2) - b * (b * g - c * e) + c * (b * e - c * d)

/-- Completing the square (LDL decomposition) with all denominators cleared. -/
lemma qf_ldl {R : Type*} [CommRing R] (a b c d e g : R) (x : Fin 3 → R) :
    a * (a * d - b ^ 2) * qf a b c d e g x =
      (a * d - b ^ 2) * (a * x 0 + b * x 1 + c * x 2) ^ 2
        + ((a * d - b ^ 2) * x 1 + (a * e - b * c) * x 2) ^ 2
        + a * det3 a b c d e g * x 2 ^ 2 := by
  simp only [qf, det3]; ring

lemma qf_nonneg_real (a b c d e g : ℝ) (ha : 0 < a) (hm : 0 < a * d - b ^ 2)
    (hD : 0 ≤ det3 a b c d e g) (x : Fin 3 → ℝ) : 0 ≤ qf a b c d e g x := by
  have h := qf_ldl a b c d e g x
  have h1 : 0 ≤ a * (a * d - b ^ 2) * qf a b c d e g x := by rw [h]; positivity
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact h1) (mul_pos ha hm)

/-- The volume of the open unit ball of `ℝ³` (Euclidean norm) is `4π/3`. -/
lemma volume_unit_ball3 :
    volume {z : Fin 3 → ℝ | ∑ i, |z i| ^ (2 : ℝ) < 1} = ENNReal.ofReal (4 * Real.pi / 3) := by
  rw [volume_sum_rpow_lt_one _ (by norm_num : (1 : ℝ) ≤ 2)]
  congr 1
  have h1 : Real.Gamma (1 / 2 + 1) = 1 / 2 * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have h2 : Real.Gamma ((Fintype.card (Fin 3) : ℝ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
    rw [Fintype.card_fin, show ((3 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), h1]; ring
  rw [h2, h1, Fintype.card_fin]
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hs0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp
  exact hs

/-- Minkowski's convex body theorem for a positive definite ternary form of determinant at
most 2: some nonzero integer vector has value below 2. -/
lemma exists_small (a b c d e g : ℝ) (ha : 0 < a) (hm : 0 < a * d - b ^ 2)
    (hD : 0 < det3 a b c d e g) (hD2 : det3 a b c d e g ≤ 2) :
    ∃ x : Fin 3 → ℤ, x ≠ 0 ∧ qf a b c d e g (fun i => (x i : ℝ)) < 2 := by
  set m := a * d - b ^ 2 with hm_def
  set D := det3 a b c d e g with hD_def
  set k := (a * e - b * c) / m
  set s1 := Real.sqrt (a / 2)
  set s2 := Real.sqrt (m / (2 * a))
  set s3 := Real.sqrt (D / (2 * m))
  have e1 : s1 ^ 2 = a / 2 := Real.sq_sqrt (by positivity)
  have e2 : s2 ^ 2 = m / (2 * a) := Real.sq_sqrt (by positivity)
  have e3 : s3 ^ 2 = D / (2 * m) := Real.sq_sqrt (by positivity)
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![s1, s1 * b / a, s1 * c / a; 0, s2, s2 * k; 0, 0, s3]
  have hS : ∀ x : Fin 3 → ℝ, ∑ i, |(M.mulVec x) i| ^ (2 : ℝ) = qf a b c d e g x / 2 := by
    intro x
    simp only [Fin.sum_univ_three, Real.rpow_two, sq_abs, M, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    have hl := qf_ldl a b c d e g x
    have ha0 : a ≠ 0 := ha.ne'
    have hm0 : m ≠ 0 := hm.ne'
    have key : qf a b c d e g x = (a * (a * x 0 + b * x 1 + c * x 2) ^ 2 * m
        + a * (m * x 1 + (a * e - b * c) * x 2) ^ 2 + a * a * D * x 2 ^ 2) / (a * a * m) := by
      rw [← hm_def, ← hD_def] at hl
      rw [eq_div_iff (by positivity)]
      linear_combination a * hl
    rw [key]
    simp only [k]
    ring_nf
    rw [e1, e2, e3]
    field_simp
    ring
  have hdetM : M.det = Real.sqrt (D / 8) := by
    rw [Matrix.det_fin_three]
    simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    simp only [s1, s2, s3, mul_zero, zero_mul, sub_zero, add_zero]
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
    norm_num
  have hdpos : 0 < Real.sqrt (D / 8) := Real.sqrt_pos.mpr (by positivity)
  have hdle : Real.sqrt (D / 8) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  set s := {x : Fin 3 → ℝ | qf a b c d e g x < 2}
  have hs : s = (Matrix.toLin' M) ⁻¹' {z : Fin 3 → ℝ | ∑ i, |z i| ^ (2 : ℝ) < 1} := by
    ext x
    simp only [s, Set.mem_ofPred_eq, Set.mem_preimage, Matrix.toLin'_apply, hS]
    constructor <;> intro h <;> linarith
  have hvol : volume s = ENNReal.ofReal ((Real.sqrt (D / 8))⁻¹ * (4 * Real.pi / 3)) := by
    have hdet0 : LinearMap.det (Matrix.toLin' M) ≠ 0 := by
      rw [LinearMap.det_toLin', hdetM]; exact hdpos.ne'
    rw [hs, Measure.addHaar_preimage_linearMap _ hdet0, volume_unit_ball3, LinearMap.det_toLin', hdetM,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr hdpos)]
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Set.mem_ofPred_eq, qf, Pi.neg_apply] at hx ⊢
    nlinarith [hx]
  have hconv : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq
    simp only [s, Set.mem_ofPred_eq] at hx hy ⊢
    have hn := qf_nonneg_real a b c d e g ha hm hD.le (x - y)
    have hid : qf a b c d e g (p • x + q • y) =
        p * qf a b c d e g x + q * qf a b c d e g y - p * q * qf a b c d e g (x - y) := by
      have : q = 1 - p := by linarith
      subst this
      simp only [qf, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hid]
    have h2 : p * qf a b c d e g x + q * qf a b c d e g y < 2 := by
      rcases hp.lt_or_eq with h | h
      · nlinarith [mul_lt_mul_of_pos_left hx h, mul_le_mul_of_nonneg_left hy.le hq]
      · subst h; nlinarith
    nlinarith [mul_nonneg (mul_nonneg hp hq) hn]
  let bas := Pi.basisFun ℝ (Fin 3)
  have fund := ZSpan.isAddFundamentalDomain' bas volume
  have : Countable (Submodule.span ℤ (Set.range bas)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range bas)))
  have hF : volume (ZSpan.fundamentalDomain bas) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hbig : volume (ZSpan.fundamentalDomain bas) * 2 ^ Module.finrank ℝ (Fin 3 → ℝ)
      < volume s := by
    rw [hF, hvol, Module.finrank_fin_fun, one_mul]
    rw [show (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 by norm_num]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hinv : 2 ≤ (Real.sqrt (D / 8))⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hdpos]; linarith
    nlinarith [Real.pi_gt_three]
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund hsymm hconv hbig
  have hmem := x.2
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : Fin 3 → ℝ) i := by
    intro i
    have := (bas.mem_span_iff_repr_mem ℤ (x : Fin 3 → ℝ)).mp hmem i
    obtain ⟨z, hz⟩ := this
    exact ⟨z, by simpa [bas] using hz⟩
  choose z hz using hint
  refine ⟨z, ?_, ?_⟩
  · intro h0
    apply hx0
    ext i
    simp [← hz i, h0]
  · have : (fun i => (z i : ℝ)) = (x : Fin 3 → ℝ) := funext hz
    rw [this]; exact hxs

/-- Integer form of `exists_small`. -/
lemma exists_small_int (a b c d e g : ℤ) (ha : 0 < a) (hm : 0 < a * d - b ^ 2)
    (hD : 0 < det3 a b c d e g) (hD2 : det3 a b c d e g ≤ 2) :
    ∃ x : Fin 3 → ℤ, x ≠ 0 ∧ qf a b c d e g x ≤ 1 := by
  obtain ⟨x, hx, h⟩ := exists_small (a : ℝ) b c d e g (by exact_mod_cast ha)
    (by exact_mod_cast hm) (by simp only [det3] at hD ⊢; exact_mod_cast hD)
    (by simp only [det3] at hD2 ⊢; exact_mod_cast hD2)
  refine ⟨x, hx, ?_⟩
  have hc : ((qf a b c d e g x : ℤ) : ℝ) = qf (a : ℝ) b c d e g (fun i => (x i : ℝ)) := by
    simp only [qf]; push_cast; ring
  have : ((qf a b c d e g x : ℤ) : ℝ) < 2 := hc ▸ h
  have : qf a b c d e g x < 2 := by exact_mod_cast this
  omega

lemma qf_pos_int (a b c d e g : ℤ) (ha : 0 < a) (hm : 0 < a * d - b ^ 2)
    (hD : 0 < det3 a b c d e g) (x : Fin 3 → ℤ) (hx : x ≠ 0) : 0 < qf a b c d e g x := by
  have h := qf_ldl a b c d e g x
  by_contra hneg
  replace hneg := not_lt.mp hneg
  have h0 : a * (a * d - b ^ 2) * qf a b c d e g x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_pos ha hm).le hneg
  rw [h] at h0
  have s1 : 0 ≤ (a * d - b ^ 2) * (a * x 0 + b * x 1 + c * x 2) ^ 2 := by positivity
  have s2 : 0 ≤ ((a * d - b ^ 2) * x 1 + (a * e - b * c) * x 2) ^ 2 := sq_nonneg _
  have s3 : 0 ≤ a * det3 a b c d e g * x 2 ^ 2 := by positivity
  have z3 : a * det3 a b c d e g * x 2 ^ 2 = 0 := by linarith
  have h2 : x 2 = 0 := by
    rcases mul_eq_zero.mp z3 with h | h
    · exact absurd h (mul_pos ha hD).ne'
    · exact pow_eq_zero_iff (by norm_num) |>.mp h
  have z2 : ((a * d - b ^ 2) * x 1 + (a * e - b * c) * x 2) ^ 2 = 0 := by linarith
  have h1 : x 1 = 0 := by
    rw [h2, mul_zero, add_zero] at z2
    rcases mul_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp z2) with h | h
    · exact absurd h hm.ne'
    · exact h
  have z1 : (a * d - b ^ 2) * (a * x 0 + b * x 1 + c * x 2) ^ 2 = 0 := by linarith
  have h0' : x 0 = 0 := by
    rw [h1, h2] at z1
    rcases mul_eq_zero.mp z1 with h | h
    · exact absurd h hm.ne'
    · have := pow_eq_zero_iff (by norm_num) |>.mp h
      simp only [mul_zero, add_zero] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' ha.ne'
      · exact h'
  apply hx
  funext i
  fin_cases i <;> simp [h0', h1, h2]

/-- The bilinear form of `qf`. -/
def bf (a b c d e g : ℤ) (x y : Fin 3 → ℤ) : ℤ :=
  a * x 0 * y 0 + d * x 1 * y 1 + g * x 2 * y 2 + b * (x 0 * y 1 + x 1 * y 0)
    + c * (x 0 * y 2 + x 2 * y 0) + e * (x 1 * y 2 + x 2 * y 1)

/-- `A x` for the Gram matrix `A`. -/
def av (a b c d e g : ℤ) (x : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![a * x 0 + b * x 1 + c * x 2, b * x 0 + d * x 1 + e * x 2, c * x 0 + e * x 1 + g * x 2]

/-- Cross product, written out. -/
def cr (p q : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![p 1 * q 2 - p 2 * q 1, p 2 * q 0 - p 0 * q 2, p 0 * q 1 - p 1 * q 0]

/-- **Unimodular ternary forms.** A positive definite integral ternary quadratic form of
determinant 1 is a sum of three squares of integral linear forms; in particular its last
diagonal coefficient `g` is a sum of three squares. -/
theorem sum_three_sq_of_det_one (a b c d e g : ℤ) (ha : 0 < a) (hm : 0 < a * d - b ^ 2)
    (hD : det3 a b c d e g = 1) :
    ∃ y : Fin 3 → ℤ, g = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  have hD0 : 0 < det3 a b c d e g := by rw [hD]; norm_num
  have hq1 : ∀ x : Fin 3 → ℤ, x ≠ 0 → 1 ≤ qf a b c d e g x := fun x hx =>
    qf_pos_int a b c d e g ha hm hD0 x hx
  -- a vector of value 1
  obtain ⟨v, hv0, hv⟩ := exists_small_int a b c d e g ha hm hD0 (by rw [hD]; norm_num)
  have hv1 : qf a b c d e g v = 1 := le_antisymm hv (hq1 v hv0)
  -- a second one, orthogonal to the first
  set u := av a b c d e g v with hu
  have hX : 0 ≤ a * u 1 ^ 2 - 2 * b * u 0 * u 1 + d * u 0 ^ 2 := by
    have h : a * (a * u 1 ^ 2 - 2 * b * u 0 * u 1 + d * u 0 ^ 2) =
        (a * u 1 - b * u 0) ^ 2 + (a * d - b ^ 2) * u 0 ^ 2 := by ring
    have : 0 ≤ a * (a * u 1 ^ 2 - 2 * b * u 0 * u 1 + d * u 0 ^ 2) := by rw [h]; positivity
    exact (mul_nonneg_iff_of_pos_left ha).mp this
  have hdet2 : det3 (a + u 0 ^ 2) (b + u 0 * u 1) (c + u 0 * u 2) (d + u 1 ^ 2)
      (e + u 1 * u 2) (g + u 2 ^ 2) = det3 a b c d e g * (1 + qf a b c d e g v) := by
    simp only [hu, av, det3, qf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hv1, hD] at hdet2
  obtain ⟨w, hw0, hw⟩ := exists_small_int (a + u 0 ^ 2) (b + u 0 * u 1) (c + u 0 * u 2)
    (d + u 1 ^ 2) (e + u 1 * u 2) (g + u 2 ^ 2) (by positivity) (by nlinarith [hX])
    (by rw [hdet2]; norm_num) (by rw [hdet2]; norm_num)
  have hsplit : qf (a + u 0 ^ 2) (b + u 0 * u 1) (c + u 0 * u 2) (d + u 1 ^ 2)
      (e + u 1 * u 2) (g + u 2 ^ 2) w = qf a b c d e g w + bf a b c d e g v w ^ 2 := by
    simp only [hu, av, qf, bf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hsplit] at hw
  have hw1' := hq1 w hw0
  have hvw : bf a b c d e g v w = 0 := by nlinarith [sq_nonneg (bf a b c d e g v w)]
  have hw1 : qf a b c d e g w = 1 := by nlinarith [sq_nonneg (bf a b c d e g v w)]
  -- the third vector: the cross product of `A v` and `A w`
  set t := cr (av a b c d e g v) (av a b c d e g w) with ht
  have hqt : qf a b c d e g t = det3 a b c d e g *
      (qf a b c d e g v * qf a b c d e g w - bf a b c d e g v w ^ 2) := by
    simp only [ht, cr, av, qf, bf, det3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hD, hv1, hw1, hvw] at hqt
  norm_num at hqt
  have hvt : bf a b c d e g v t = 0 := by
    simp only [ht, cr, av, bf, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hwt : bf a b c d e g w t = 0 := by
    simp only [ht, cr, av, bf, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hbq : ∀ x, bf a b c d e g x x = qf a b c d e g x := fun x => by simp only [bf, qf]; ring
  have hbs : ∀ x y, bf a b c d e g x y = bf a b c d e g y x := fun x y => by
    simp only [bf]; ring
  have hwv : bf a b c d e g w v = 0 := by rw [hbs]; exact hvw
  have htv : bf a b c d e g t v = 0 := by rw [hbs]; exact hvt
  have htw : bf a b c d e g t w = 0 := by rw [hbs]; exact hwt
  -- the change of basis `P = [v w t]` is an isometry onto the sum of three squares
  let A : Matrix (Fin 3) (Fin 3) ℤ := !![a, b, c; b, d, e; c, e, g]
  let P : Matrix (Fin 3) (Fin 3) ℤ := (Matrix.of ![v, w, t])ᵀ
  have hentry : ∀ i j, (Pᵀ * A * P) i j = bf a b c d e g (![v, w, t] i) (![v, w, t] j) := by
    intro i j
    simp only [P, A, Matrix.transpose_transpose, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply, Matrix.of_apply, bf]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    ring
  have hPAP : (Pᵀ * A) * P = 1 := by
    ext i j
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [hbq, hv1, hw1, hqt, hvw, hvt, hwt, hwv, htv, htw]
  have hPPA : P * (Pᵀ * A) = 1 := mul_eq_one_comm.mp hPAP
  let x : Fin 3 → ℤ := ![0, 0, 1]
  let y := (Pᵀ * A).mulVec x
  have hPy : P.mulVec y = x := by
    simp only [y, Matrix.mulVec_mulVec, hPPA, Matrix.one_mulVec]
  have hg : g = x ⬝ᵥ A.mulVec x := by
    simp [x, A, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨y, ?_⟩
  have hyy : x ⬝ᵥ A.mulVec x = y ⬝ᵥ y := by
    conv_lhs => rw [← hPy]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_comm]
    simp only [y, Matrix.mulVec_mulVec]
    rw [hPPA, Matrix.mul_one]
  rw [hg, hyy]
  simp [dotProduct, Fin.sum_univ_three, sq]

/-! ### Quadratic residues from Dirichlet's theorem -/

lemma coprime_four_mul (r n k c : ℕ) (h : k * r + 1 = c * n) (hr : r % 2 = 1) :
    Nat.Coprime r (4 * n) := by
  apply Nat.Coprime.mul_right
  · rcases (show r % 4 = 1 ∨ r % 4 = 3 by omega) with h4 | h4
    · exact Nat.isCoprime_iff_coprime.mp ⟨1, -((r / 4 : ℕ) : ℤ), by
        have := Nat.div_add_mod r 4; rw [h4] at this; push_cast; omega⟩
    · exact Nat.isCoprime_iff_coprime.mp ⟨-1, ((r / 4 : ℕ) : ℤ) + 1, by
        have := Nat.div_add_mod r 4; rw [h4] at this; push_cast; omega⟩
  · exact Nat.isCoprime_iff_coprime.mp ⟨-(k : ℤ), c, by
      have : ((k * r + 1 : ℕ) : ℤ) = ((c * n : ℕ) : ℤ) := by rw [h]
      push_cast at this; linarith⟩

/-- Dirichlet's theorem in the form used here. -/
lemma exists_prime_eq (n r : ℕ) (hn : 0 < n) (hr : r < 4 * n) (hc : Nat.Coprime r (4 * n)) :
    ∃ p j : ℕ, p.Prime ∧ p = 4 * n * j + r := by
  have : NeZero (4 * n) := ⟨by omega⟩
  obtain ⟨p, -, hp, hpm⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime r (4 * n)).mpr hc) 0
  refine ⟨p, p / (4 * n), hp, ?_⟩
  have h1 := (ZMod.natCast_eq_natCast_iff' p r (4 * n)).mp hpm
  rw [Nat.mod_eq_of_lt hr] at h1
  have := Nat.div_add_mod p (4 * n)
  rw [h1] at this
  linarith

/-- A square root of `D` modulo a prime `p` from `J(D | p) = 1`. -/
lemma exists_sq_of_jacobi (p : ℕ) [Fact p.Prime] (D : ℤ) (h : jacobiSym D p = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - D := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have h0 : (D : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p D).mpr h0] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p h0).mp h
  refine ⟨(r.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val, hr]; ring

lemma jacobi_neg_one_mod (d : ℕ) (x : ℤ) (n : ℤ) (hx : x + 1 = d * n) :
    jacobiSym x d = jacobiSym (-1) d := by
  apply jacobiSym.mod_left'
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  rw [show x - -1 = (d : ℤ) * n by linarith]
  exact Int.mul_emod_right _ _

/-- Case `n ≡ 2 (mod 4)`: a prime `p = d n - 1` with `-d` a square modulo `p`. -/
lemma key_two_mod_four (n : ℕ) (hn : n % 4 = 2) :
    ∃ d t : ℤ, 0 < d ∧ 0 < d * n - 1 ∧ (d * n - 1) ∣ t ^ 2 + d := by
  obtain ⟨p, j, hp, hpj⟩ := exists_prime_eq n (n - 1) (by omega) (by omega)
    (coprime_four_mul (n - 1) n 1 1 (by omega) (by omega))
  have : Fact p.Prime := ⟨hp⟩
  have hpj' : p = 4 * (n * j) + (n - 1) := by rw [hpj]; ring
  set d : ℕ := 4 * j + 1 with hd
  have hdn : (p : ℤ) + 1 = d * n := by
    have : p + 1 = d * n := by
      rw [hd, hpj]; have : 1 ≤ n := by omega
      zify [this]; ring
    exact_mod_cast this
  have hp4 : p % 4 = 1 := by generalize n * j = N at hpj'; omega
  have hd4 : d % 4 = 1 := by omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hJ : jacobiSym (-(d : ℤ)) p = 1 := by
    rw [show (-(d : ℤ)) = -1 * d by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hpodd,
      ZMod.χ₄_nat_one_mod_four hp4, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four hd4 hpodd,
      jacobi_neg_one_mod d p n hdn, jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_one_mod_four hd4]
  obtain ⟨t, ht⟩ := exists_sq_of_jacobi p _ hJ
  refine ⟨d, t, by positivity, ?_, ?_⟩
  · have := hp.two_le; omega
  · rw [show (d : ℤ) * n - 1 = p by linarith]
    simpa using ht

/-- Case `n` odd, `n ≢ 7 (mod 8)`: `2p = d n - 1` with `p` prime and `-d` a square mod `2p`. -/
lemma key_odd (n c : ℕ) (hnc : (c = 1 ∧ n % 8 = 3) ∨ (c = 3 ∧ (n % 8 = 1 ∨ n % 8 = 5))) :
    ∃ d t : ℤ, 0 < d ∧ 0 < d * n - 1 ∧ (d * n - 1) ∣ t ^ 2 + d := by
  have hcn8 : (c * n) % 8 = 3 ∨ (c * n) % 8 = 7 := by
    rcases hnc with ⟨rfl, h⟩ | ⟨rfl, h | h⟩ <;> omega
  set r := c * n / 2 with hr
  have hr2 : 2 * r + 1 = c * n := by generalize c * n = M at hr hcn8 ⊢; omega
  have hrodd : r % 2 = 1 := by generalize c * n = M at hr hcn8 ⊢; omega
  have hc3 : c ≤ 3 := by omega
  have hn0 : 0 < n := by omega
  have hrlt : r < 4 * n := by
    have : c * n ≤ 3 * n := Nat.mul_le_mul_right n hc3
    omega
  obtain ⟨p, j, hp, hpj⟩ := exists_prime_eq n r hn0 hrlt
    (coprime_four_mul r n 2 c hr2 hrodd)
  have : Fact p.Prime := ⟨hp⟩
  set d : ℕ := 8 * j + c with hd
  have hdn : 2 * p + 1 = d * n := by
    rw [hd, hpj, add_mul, ← hr2]; ring
  have hdn' : (2 * p : ℤ) + 1 = d * n := by exact_mod_cast hdn
  have hd8 : d % 8 = c := by omega
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hp8 : (2 * p + 1) % 8 = (c * (n % 8)) % 8 := by
    rw [hdn, Nat.mul_mod, hd8]
  have hp4 : (c = 1 ∧ p % 4 = 1) ∨ (c = 3 ∧ p % 4 = 1) ∨ (c = 3 ∧ p % 4 = 3) := by
    rcases hnc with ⟨rfl, h⟩ | ⟨rfl, h | h⟩ <;> rw [h] at hp8 <;> omega
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  -- `J(p | d) = 1`
  have hpd : jacobiSym p d = 1 := by
    have h2 := jacobi_neg_one_mod d (2 * p) n hdn'
    rw [jacobiSym.mul_left, jacobiSym.at_two hdodd, jacobiSym.at_neg_one hdodd,
      ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four] at h2
    have hd2 : d % 2 = 1 := by omega
    rcases hnc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have hd4 : d % 4 = 1 := by omega
      simpa [hd2, hd4, hd8] using h2
    · have hd4 : d % 4 = 3 := by omega
      have : jacobiSym p d = 1 := by
        simp [hd2, hd4, hd8] at h2
        exact h2
      exact this
  have hJ : jacobiSym (-(d : ℤ)) p = 1 := by
    rw [show (-(d : ℤ)) = -1 * d by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hpodd]
    rcases hp4 with ⟨-, h4⟩ | ⟨-, h4⟩ | ⟨hc, h4⟩
    · rw [ZMod.χ₄_nat_one_mod_four h4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hdodd h4, hpd]
    · rw [ZMod.χ₄_nat_one_mod_four h4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hdodd h4, hpd]
    · rw [ZMod.χ₄_nat_three_mod_four h4,
        jacobiSym.quadratic_reciprocity_three_mod_four (by omega) h4, hpd]
      norm_num
  obtain ⟨t, ht⟩ := exists_sq_of_jacobi p _ hJ
  simp only [sub_neg_eq_add] at ht
  -- make the root odd, so that `t ^ 2 + d` is even
  obtain ⟨s, hs, hsodd⟩ : ∃ s : ℤ, (p : ℤ) ∣ s ^ 2 + d ∧ s % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one t with h | h
    · refine ⟨t + p, ?_, by omega⟩
      have : (t + p) ^ 2 + d = (t ^ 2 + d) + p * (2 * t + p) := by ring
      rw [this]; exact dvd_add ht (dvd_mul_right _ _)
    · exact ⟨t, ht, h⟩
  have hd0 : (0 : ℤ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  refine ⟨d, s, hd0, by omega, ?_⟩
  rw [show (d : ℤ) * n - 1 = 2 * p by linarith]
  obtain ⟨k, hk⟩ := hs
  have hs2 : (s ^ 2 + d) % 2 = 0 := by
    have : s ^ 2 % 2 = 1 := by rw [pow_two, Int.mul_emod, hsodd]; norm_num
    have hd2 : (d : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hdodd
    omega
  have hk2 : k % 2 = 0 := by
    rw [hk, Int.mul_emod] at hs2
    have : (p : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hpodd
    rw [this, one_mul, Int.emod_emod_of_dvd _ (by norm_num)] at hs2
    exact hs2
  obtain ⟨k', rfl⟩ : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hk2
  exact ⟨k', by rw [hk]; ring⟩

/-! ### Legendre's three-square theorem -/

/-- The quadratic form `[[a, t, 1], [t, d n - 1, 0], [1, 0, n]]` has determinant 1. -/
lemma sum_three_sq_of_key (n : ℕ) (d t : ℤ) (hd : 0 < d) (hp : 0 < d * n - 1)
    (hdvd : (d * n - 1) ∣ t ^ 2 + d) : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨a, ha⟩ := hdvd
  have ha0 : 0 < a := by
    have : 0 < (d * n - 1) * a := by rw [← ha]; positivity
    exact pos_of_mul_pos_right this hp.le
  obtain ⟨y, hy⟩ := sum_three_sq_of_det_one a t 1 (d * n - 1) 0 n ha0
    (by nlinarith) (by simp only [det3]; linear_combination (-(n : ℤ)) * ha)
  exact ⟨y 0, y 1, y 2, hy.symm⟩

/-- **Legendre**, hard direction for `n ≢ 0, 4, 7 (mod 8)`. -/
theorem sum_three_sq_of_mod_eight (n : ℕ)
    (hn : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨d, t, hd, hp, hdvd⟩ : ∃ d t : ℤ, 0 < d ∧ 0 < d * n - 1 ∧ (d * n - 1) ∣ t ^ 2 + d := by
    rcases hn with h | h | h | h | h
    · exact key_odd n 3 (Or.inr ⟨rfl, Or.inl h⟩)
    · exact key_two_mod_four n (by omega)
    · exact key_odd n 1 (Or.inl ⟨rfl, h⟩)
    · exact key_odd n 3 (Or.inr ⟨rfl, Or.inr h⟩)
    · exact key_two_mod_four n (by omega)
  exact sum_three_sq_of_key n d t hd hp hdvd

lemma sq_mod_eight (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h := Nat.mod_lt x (show 8 > 0 by norm_num)
  rw [Nat.pow_mod]
  interval_cases x % 8 <;> simp

lemma sq_mod_four (x : ℕ) : (x % 2 = 0 ∧ x ^ 2 % 4 = 0) ∨ (x % 2 = 1 ∧ x ^ 2 % 4 = 1) := by
  have h := Nat.mod_lt x (show 4 > 0 by norm_num)
  have h2 : x % 2 = x % 4 % 2 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  rw [Nat.pow_mod, h2]
  interval_cases x % 4 <;> simp

/-- **Legendre**, easy direction: `4^a (8b+7)` is not a sum of three squares. -/
theorem not_sum_three_sq (a b : ℕ) :
    ∀ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 ≠ 4 ^ a * (8 * b + 7) := by
  induction a with
  | zero =>
    intro x y z h
    rcases sq_mod_eight x with hx | hx | hx <;> rcases sq_mod_eight y with hy | hy | hy <;>
      rcases sq_mod_eight z with hz | hz | hz <;> simp at h <;> omega
  | succ a ih =>
    intro x y z h
    have h4 : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by
      rw [h, pow_succ]; simp [Nat.mul_mod, Nat.mul_assoc]
    obtain ⟨x', rfl⟩ : 2 ∣ x := Nat.dvd_of_mod_eq_zero (by
      rcases sq_mod_four x with hx | hx <;> rcases sq_mod_four y with hy | hy <;>
        rcases sq_mod_four z with hz | hz <;> omega)
    obtain ⟨y', rfl⟩ : 2 ∣ y := Nat.dvd_of_mod_eq_zero (by
      rcases sq_mod_four (2 * x') with hx | hx <;> rcases sq_mod_four y with hy | hy <;>
        rcases sq_mod_four z with hz | hz <;> omega)
    obtain ⟨z', rfl⟩ : 2 ∣ z := Nat.dvd_of_mod_eq_zero (by
      rcases sq_mod_four (2 * x') with hx | hx <;> rcases sq_mod_four (2 * y') with hy | hy <;>
        rcases sq_mod_four z with hz | hz <;> omega)
    apply ih x' y' z'
    have : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * (4 ^ a * (8 * b + 7)) := by
      have e1 : 4 ^ (a + 1) * (8 * b + 7) = 4 * (4 ^ a * (8 * b + 7)) := by ring
      have e2 : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = (2 * x') ^ 2 + (2 * y') ^ 2 + (2 * z') ^ 2 := by
        ring
      rw [e2, h, e1]
    omega

/-- **Legendre's three-square theorem** over `ℕ`. -/
theorem sum_three_sq_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  constructor
  · rintro ⟨x, y, z, h⟩ ⟨a, b, rfl⟩
    exact not_sum_three_sq a b x y z h
  · intro hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact ⟨0, 0, 0, rfl⟩
      by_cases h4 : n % 4 = 0
      · obtain ⟨m, rfl⟩ : 4 ∣ n := Nat.dvd_of_mod_eq_zero h4
        obtain ⟨x, y, z, h⟩ := ih m (by omega) (by
          rintro ⟨a, b, rfl⟩; exact hn ⟨a + 1, b, by rw [pow_succ]; ring⟩)
        exact ⟨2 * x, 2 * y, 2 * z, by rw [← h]; ring⟩
      · have h7 : n % 8 ≠ 7 := fun h7 => hn ⟨0, n / 8, by omega⟩
        obtain ⟨x, y, z, h⟩ := sum_three_sq_of_mod_eight n (by omega)
        refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
        have : ((x.natAbs ^ 2 + y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) : ℤ) = n := by
          push_cast; simpa [Int.natAbs_sq] using h
        exact_mod_cast this

/-- **Legendre's three-square theorem** over `ℤ`. -/
theorem sum_three_sq_iff_int (n : ℤ) :
    (∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔
      0 ≤ n ∧ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  constructor
  · rintro ⟨x, y, z, h⟩
    have h0 : 0 ≤ n := by rw [← h]; positivity
    refine ⟨h0, ?_⟩
    have := (sum_three_sq_iff n.toNat).mp ⟨x.natAbs, y.natAbs, z.natAbs, by
      have : ((x.natAbs ^ 2 + y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) : ℤ) = (n.toNat : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg h0]; simpa [Int.natAbs_sq] using h
      exact_mod_cast this⟩
    rintro ⟨a, b, rfl⟩
    exact this ⟨a, b, by
      have : ((4 ^ a * (8 * b + 7) : ℕ) : ℤ) = 4 ^ a * (8 * b + 7) := by push_cast; ring
      rw [← this, Int.toNat_natCast]⟩
  · rintro ⟨h0, hn⟩
    obtain ⟨x, y, z, h⟩ := (sum_three_sq_iff n.toNat).mpr (by
      rintro ⟨a, b, hab⟩
      exact hn ⟨a, b, by rw [← Int.toNat_of_nonneg h0, hab]; push_cast; ring⟩)
    exact ⟨x, y, z, by rw [← Int.toNat_of_nonneg h0, ← h]; push_cast; ring⟩

end OpenProblemsLib.ThreeSquares
