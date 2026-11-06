/-
OEIS A129756: a(n) = 1 + 2 floor(n/4) (offset 0).  Conjecture (Michel Lagneau,
entry text): number of roots of P(x) = x^n - x^(n-1) - ... - x - 1 in the
right half-plane.  Proved here with the polynomial of degree n + 1.

Main theorems.
* `A129756_roots`: for every n, the multiset of complex roots of
  `Pp (n+1) = X^(n+1) - Σ_{j<n+1} X^j` has exactly `a n = 1 + 2 * (n / 4)`
  elements (with multiplicity) with positive real part.
* `P_count`: for n ≥ 1, the count for `Pp n` is 1 + 2 floor((n-1)/4).
* `A083219_roots`: the count in the open left half-plane is n - 2 floor(n/4)
  (the companion conjecture in A083219, same index shift).

Method.  Q = (X - 1) P = X^(n+1) - 2 X^n + 1 (`Qp_factor`).  `Q_im`, `Q_re`:
explicit real and imaginary parts of Q(iy) by n mod 4; so Q(iy) is never real
for y ≠ 0 and Q(0) = 1, hence Q(iy) stays in the slit plane (`Q_slit`) and no
root lies on the imaginary axis (`S_re_ne`).  Writing Q(iy) = Π (iy - r) over
the roots, each factor has the explicit continuous argument
`th r y = arctan ((y - Im r)/(-Re r)) (+ π if Re r > 0)` (`th_angle`).
arg Q(iy) minus Σ th r y is continuous with values in 2πℤ, hence constant
(`const_of_angle_zero`); with arg Q(-iY) = -arg Q(iY) this gives
2 arg Q(iY) = Σ_r (th r Y - th r (-Y)) (`two_arg`).  As Y → ∞ each summand
tends to π (Re r < 0) or -π (Re r > 0) (`D_tendsto`), while the signs of
Re Q(iY), Im Q(iY) for Y > 1 confine 2 arg Q(iY) to an interval of length π
(`count_Q`); with N_L + N_R = n + 1 the parity fixes N_R.

Not checked here: agreement with the OEIS b-file (certificate/rhp.gp checks
degrees 1..120 numerically).
-/
import Mathlib

open Finset Complex Filter Topology Polynomial
open scoped Real

namespace A129756

/-- The n-bonacci polynomial. -/
noncomputable def P (n : ℕ) (z : ℂ) : ℂ := z ^ n - ∑ j ∈ range n, z ^ j

/-- (z - 1) P(z). -/
noncomputable def Q (n : ℕ) (z : ℂ) : ℂ := z ^ (n + 1) - 2 * z ^ n + 1

theorem factor (n : ℕ) (z : ℂ) : (z - 1) * P n z = Q n z := by
  unfold P Q
  have h := geom_sum_mul z n
  linear_combination (-1 : ℂ) * h

theorem I_mul_pow (m k : ℕ) (y : ℝ) :
    (I * (y : ℂ)) ^ (4 * m + k) = I ^ k * ((y ^ (4 * m + k) : ℝ) : ℂ) := by
  rw [mul_pow, pow_add I, pow_mul, I_pow_four, one_pow, one_mul]
  push_cast
  rfl

theorem Q_im (m : ℕ) (y : ℝ) :
    (Q (4 * m) (I * y)).im = y ^ (4 * m + 1) ∧
    (Q (4 * m + 1) (I * y)).im = -2 * y ^ (4 * m + 1) ∧
    (Q (4 * m + 2) (I * y)).im = -y ^ (4 * m + 3) ∧
    (Q (4 * m + 3) (I * y)).im = 2 * y ^ (4 * m + 3) := by
  have k0 : (I * (y : ℂ)) ^ (4 * m) = ((y ^ (4 * m) : ℝ) : ℂ) := by
    have := I_mul_pow m 0 y
    simpa using this
  have k1 := I_mul_pow m 1 y
  have k2 := I_mul_pow m 2 y
  have k3 := I_mul_pow m 3 y
  have k4 := I_mul_pow m 4 y
  have e4 : 4 * m + 3 + 1 = 4 * m + 4 := rfl
  have e3 : 4 * m + 2 + 1 = 4 * m + 3 := rfl
  have e2 : 4 * m + 1 + 1 = 4 * m + 2 := rfl
  unfold Q
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k1, k0]
    generalize y ^ (4 * m + 1) = A
    generalize y ^ (4 * m) = B
    simp
  · rw [e2, k2, k1]
    generalize y ^ (4 * m + 2) = A
    generalize y ^ (4 * m + 1) = B
    simp [pow_two]
  · rw [e3, k3, k2]
    generalize y ^ (4 * m + 3) = A
    generalize y ^ (4 * m + 2) = B
    simp [pow_succ]
  · rw [e4, k4, k3]
    generalize y ^ (4 * m + 4) = A
    generalize y ^ (4 * m + 3) = B
    simp [pow_succ]

theorem Q_im_ne_zero (n : ℕ) (y : ℝ) (hy : y ≠ 0) : (Q n (I * y)).im ≠ 0 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod n 4).symm⟩
  have h := Q_im m y
  interval_cases r
  · rw [Nat.add_zero, h.1]; exact pow_ne_zero _ hy
  · rw [h.2.1]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hy)
  · rw [h.2.2.1]; exact neg_ne_zero.mpr (pow_ne_zero _ hy)
  · rw [h.2.2.2]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hy)

theorem Q_ne_zero_imag (n : ℕ) (y : ℝ) : Q n (I * y) ≠ 0 := by
  by_cases hy : y = 0
  · subst hy
    unfold Q
    rcases n with _ | n
    · norm_num
    · simp
  · intro h
    exact Q_im_ne_zero n y hy (by rw [h]; rfl)

theorem Q_im_pos (m : ℕ) (y : ℝ) (hy : 0 < y) :
    0 < (Q (4 * m) (I * y)).im ∧ 0 < (Q (4 * m + 3) (I * y)).im := by
  have h := Q_im m y
  rw [h.1, h.2.2.2]
  exact ⟨pow_pos hy _, by positivity⟩

theorem Q_im_neg (m : ℕ) (y : ℝ) (hy : 0 < y) :
    (Q (4 * m + 1) (I * y)).im < 0 ∧ (Q (4 * m + 2) (I * y)).im < 0 := by
  have h := Q_im m y
  rw [h.2.1, h.2.2.1]
  exact ⟨by nlinarith [pow_pos hy (4 * m + 1)], by nlinarith [pow_pos hy (4 * m + 3)]⟩

/-! Real parts. -/

theorem Q_re (m : ℕ) (y : ℝ) :
    (Q (4 * m) (I * y)).re = 1 - 2 * y ^ (4 * m) ∧
    (Q (4 * m + 1) (I * y)).re = 1 - y ^ (4 * m + 2) ∧
    (Q (4 * m + 2) (I * y)).re = 1 + 2 * y ^ (4 * m + 2) ∧
    (Q (4 * m + 3) (I * y)).re = 1 + y ^ (4 * m + 4) := by
  have k0 : (I * (y : ℂ)) ^ (4 * m) = ((y ^ (4 * m) : ℝ) : ℂ) := by
    have := I_mul_pow m 0 y
    simpa using this
  have k1 := I_mul_pow m 1 y
  have k2 := I_mul_pow m 2 y
  have k3 := I_mul_pow m 3 y
  have k4 := I_mul_pow m 4 y
  have e4 : 4 * m + 3 + 1 = 4 * m + 4 := rfl
  have e3 : 4 * m + 2 + 1 = 4 * m + 3 := rfl
  have e2 : 4 * m + 1 + 1 = 4 * m + 2 := rfl
  unfold Q
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k1, k0]
    generalize y ^ (4 * m + 1) = A
    generalize y ^ (4 * m) = B
    simp
    ring
  · rw [e2, k2, k1]
    generalize y ^ (4 * m + 2) = A
    generalize y ^ (4 * m + 1) = B
    simp [pow_two]
    ring
  · rw [e3, k3, k2]
    generalize y ^ (4 * m + 3) = A
    generalize y ^ (4 * m + 2) = B
    simp [pow_succ]
    ring
  · rw [e4, k4, k3]
    generalize y ^ (4 * m + 4) = A
    generalize y ^ (4 * m + 3) = B
    simp [pow_succ]
    ring

/-! Polynomials and roots. -/

/-- Q as a polynomial. -/
noncomputable def Qp (n : ℕ) : ℂ[X] := X ^ (n + 1) - 2 * X ^ n + 1

/-- P as a polynomial. -/
noncomputable def Pp (n : ℕ) : ℂ[X] := X ^ n - ∑ j ∈ range n, X ^ j

/-- The roots of Q, with multiplicity. -/
noncomputable def S (n : ℕ) : Multiset ℂ := (Qp n).roots

theorem Qp_eval (n : ℕ) (z : ℂ) : (Qp n).eval z = Q n z := by
  simp [Qp, Q]

theorem Qp_monic (n : ℕ) : (Qp n).Monic := by
  unfold Qp
  monicity!

theorem Qp_natDegree (n : ℕ) : (Qp n).natDegree = n + 1 := by
  unfold Qp
  compute_degree!

theorem Qp_factor (n : ℕ) : (X - C 1) * Pp n = Qp n := by
  unfold Pp Qp
  have h := geom_sum_mul (X : ℂ[X]) n
  rw [map_one]
  linear_combination (-1 : ℂ[X]) * h

theorem card_S (n : ℕ) : (S n).card = n + 1 := by
  unfold S
  rw [IsAlgClosed.card_roots_eq_natDegree, Qp_natDegree]

theorem Q_prod (n : ℕ) (z : ℂ) : Q n z = ((S n).map (fun r => z - r)).prod := by
  rw [← Qp_eval]
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Qp_monic n)
    (by rw [IsAlgClosed.card_roots_eq_natDegree])
  nth_rewrite 1 [← h]
  rw [eval_multiset_prod, Multiset.map_map]
  unfold S
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  simp

theorem S_re_ne (n : ℕ) {r : ℂ} (hr : r ∈ S n) : r.re ≠ 0 := by
  intro h0
  have hroot : (Qp n).eval r = 0 := ((mem_roots (Qp_monic n).ne_zero).mp hr)
  have e : r = I * ((r.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [h0]
  rw [Qp_eval, e] at hroot
  exact Q_ne_zero_imag n r.im hroot

theorem fac_ne (r : ℂ) (hr : r.re ≠ 0) (y : ℝ) : I * (y : ℂ) - r ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact hr (by linarith)

/-! Continuous argument of one factor iy - r. -/

/-- A continuous argument of I*y - r (for r.re ≠ 0). -/
noncomputable def th (r : ℂ) (y : ℝ) : ℝ :=
  Real.arctan ((y - r.im) / (-r.re)) + (if 0 < r.re then π else 0)

theorem arg_eq_arctan {w : ℂ} (hw : 0 < w.re) : arg w = Real.arctan (w.im / w.re) := by
  have h := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [← tan_arg]
  exact (Real.arctan_tan (abs_lt.mp h).1 (abs_lt.mp h).2).symm

theorem th_angle (r : ℂ) (hr : r.re ≠ 0) (y : ℝ) :
    (th r y : Real.Angle) = (arg (I * (y : ℂ) - r) : Real.Angle) := by
  unfold th
  rcases lt_or_gt_of_ne hr with h | h
  · have hw : 0 < (I * (y : ℂ) - r).re := by simp; linarith
    simp only [show ¬ (0 < r.re) from not_lt.mpr h.le, ↓reduceIte, add_zero]
    rw [arg_eq_arctan hw]
    congr 2
    simp
  · have hw : 0 < (-(I * (y : ℂ) - r)).re := by simp; linarith
    have hne : -(I * (y : ℂ) - r) ≠ 0 := by
      intro h0
      rw [h0] at hw
      simp at hw
    simp only [h, ↓reduceIte]
    rw [Real.Angle.coe_add]
    have h2 := arg_neg_coe_angle hne
    rw [neg_neg] at h2
    rw [h2, arg_eq_arctan hw]
    congr 3
    simp
    ring

theorem th_continuous (r : ℂ) : Continuous (th r) := by
  unfold th
  exact (Real.continuous_arctan.comp ((continuous_id.sub continuous_const).div_const _)).add
    continuous_const

theorem angle_sum (s : Multiset ℂ) (y : ℝ) (hs : ∀ r ∈ s, r.re ≠ 0) :
    (((s.map (fun r => th r y)).sum : ℝ) : Real.Angle) =
      (arg ((s.map (fun r => I * (y : ℂ) - r)).prod) : Real.Angle) ∧
    (s.map (fun r => I * (y : ℂ) - r)).prod ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a.re ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun r hr => hs r (Multiset.mem_cons_of_mem hr))
    have hfa := fac_ne a ha y
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    refine ⟨?_, mul_ne_zero hfa ih'.2⟩
    rw [Real.Angle.coe_add, ih'.1, th_angle a ha y, arg_mul_coe_angle hfa ih'.2]

/-- A continuous real function with values in 2πℤ is constant. -/
theorem const_of_angle_zero (g : ℝ → ℝ) (hg : Continuous g) (h : ∀ y, (g y : Real.Angle) = 0)
    (a b : ℝ) : g a = g b := by
  have key : ∀ a b : ℝ, ∀ ka kb : ℤ, (ka : ℝ) * (2 * π) = g a → (kb : ℝ) * (2 * π) = g b →
      ka < kb → False := by
    intro a b ka kb ha hb hlt
    have hpi := Real.pi_pos
    have hk : (ka : ℝ) + 1 ≤ kb := by exact_mod_cast hlt
    have hv : ((ka : ℝ) + 1 / 2) * (2 * π) ∈ Set.uIcc (g a) (g b) := by
      rw [Set.mem_uIcc]
      left
      constructor <;> nlinarith
    obtain ⟨y, -, hy⟩ := intermediate_value_uIcc hg.continuousOn hv
    obtain ⟨k, hk'⟩ := Real.Angle.coe_eq_zero_iff.mp (h y)
    rw [zsmul_eq_mul, hy] at hk'
    have h2 : (k : ℝ) = ka + 1 / 2 := by
      have := mul_right_cancel₀ (by positivity : (2 * π) ≠ 0) hk'
      exact this
    have h3 : ((2 * k : ℤ) : ℝ) = ((2 * ka + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h4 : 2 * k = 2 * ka + 1 := by exact_mod_cast h3
    omega
  obtain ⟨ka, hka⟩ := Real.Angle.coe_eq_zero_iff.mp (h a)
  obtain ⟨kb, hkb⟩ := Real.Angle.coe_eq_zero_iff.mp (h b)
  rw [zsmul_eq_mul] at hka hkb
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact (key a b ka kb hka hkb hlt).elim
  · rw [← hka, ← hkb, heq]
  · exact (key b a kb ka hkb hka hgt).elim

theorem Q_slit (n : ℕ) (hn : 1 ≤ n) (y : ℝ) : Q n (I * y) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hy : y = 0
  · left
    subst hy
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [Q]
  · right
    exact Q_im_ne_zero n y hy

theorem Q_conj (n : ℕ) (Y : ℝ) : Q n (I * ((-Y : ℝ) : ℂ)) = (starRingEnd ℂ) (Q n (I * Y)) := by
  simp [Q, map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem two_arg (n : ℕ) (hn : 1 ≤ n) (Y : ℝ) :
    2 * arg (Q n (I * Y)) = ((S n).map (fun r => th r Y - th r (-Y))).sum := by
  have hS : ∀ r ∈ S n, r.re ≠ 0 := fun r hr => S_re_ne n hr
  set g : ℝ → ℝ := fun y => arg (Q n (I * y)) - ((S n).map (fun r => th r y)).sum with hgdef
  have hg0 : ∀ y, (g y : Real.Angle) = 0 := by
    intro y
    simp only [hgdef, Real.Angle.coe_sub]
    rw [(angle_sum (S n) y hS).1, ← Q_prod, sub_self]
  have hgc : Continuous g := by
    apply Continuous.sub
    · rw [continuous_iff_continuousAt]
      intro y
      have hc : Continuous (fun y : ℝ => Q n (I * (y : ℂ))) := by
        unfold Q
        fun_prop
      exact ContinuousAt.comp (g := arg) (f := fun y : ℝ => Q n (I * (y : ℂ)))
        (continuousAt_arg (Q_slit n hn y)) hc.continuousAt
    · exact continuous_multiset_sum _ (fun r _ => th_continuous r)
  have hc := const_of_angle_zero g hgc hg0 Y (-Y)
  have hneg : arg (Q n (I * ((-Y : ℝ) : ℂ))) = - arg (Q n (I * Y)) := by
    rw [Q_conj, arg_conj]
    have hnp : arg (Q n (I * Y)) ≠ π := by
      intro hpi
      have := Q_slit n hn Y
      rw [mem_slitPlane_iff] at this
      rw [arg_eq_pi_iff] at hpi
      rcases this with h1 | h1
      · linarith [hpi.1]
      · exact h1 hpi.2
    simp only [hnp, ↓reduceIte]
  simp only [hgdef] at hc
  rw [hneg] at hc
  rw [Multiset.sum_map_sub]
  linarith

/-! Limits as Y → ∞. -/

/-- Limit of th r Y - th r (-Y): π for a root in the left half-plane, -π in the right. -/
noncomputable def L (r : ℂ) : ℝ := if 0 < r.re then -π else π

theorem D_tendsto (r : ℂ) (hr : r.re ≠ 0) :
    Tendsto (fun Y : ℝ => th r Y - th r (-Y)) atTop (𝓝 (L r)) := by
  have e : (fun Y : ℝ => th r Y - th r (-Y)) =
      fun Y => Real.arctan ((Y - r.im) / (-r.re)) - Real.arctan ((-Y - r.im) / (-r.re)) := by
    funext Y
    unfold th
    ring
  rw [e]
  have u1 : Tendsto (fun Y : ℝ => Y - r.im) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-r.im) tendsto_id
  have u2 : Tendsto (fun Y : ℝ => -Y - r.im) atTop atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atTop (-r.im) tendsto_neg_atTop_atBot
  have hTop := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have hBot := Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds
  rcases lt_or_gt_of_ne hr with h | h
  · have hc : 0 < -r.re := by linarith
    have t1 := hTop.comp (u1.atTop_div_const hc)
    have t2 := hBot.comp (u2.atBot_div_const hc)
    have := t1.sub t2
    unfold L
    simp only [show ¬ (0 < r.re) from not_lt.mpr h.le, ↓reduceIte]
    have hv : π = π / 2 - -(π / 2) := by ring
    rw [hv]
    exact this
  · have hc : -r.re < 0 := by linarith
    have u3 : Tendsto (fun Y : ℝ => Y + r.im) atTop atTop :=
      tendsto_atTop_add_const_right atTop r.im tendsto_id
    have t1 := hBot.comp (u1.atTop_div_const_of_neg hc)
    have t2 : Tendsto (fun Y : ℝ => Real.arctan ((-Y - r.im) / (-r.re))) atTop (𝓝 (π / 2)) := by
      refine (hTop.comp (u3.atTop_div_const h)).congr (fun Y => ?_)
      simp only [Function.comp]
      rw [show -Y - r.im = -(Y + r.im) by ring, neg_div_neg_eq]
    have := t1.sub t2
    unfold L
    simp only [h, ↓reduceIte]
    have hv : -π = -(π / 2) - π / 2 := by ring
    rw [hv]
    exact this

theorem sumL (s : Multiset ℂ) :
    (s.map L).sum = π * ((s.countP (fun r => ¬ 0 < r.re) : ℝ) - (s.countP (fun r => 0 < r.re) : ℝ)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih]
    unfold L
    by_cases h : 0 < a.re
    · simp [h]; ring
    · simp [h]; ring

theorem limit_eq (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun Y : ℝ => 2 * arg (Q n (I * Y))) atTop
      (𝓝 (π * (((S n).countP (fun r => ¬ 0 < r.re) : ℝ) - ((S n).countP (fun r => 0 < r.re) : ℝ)))) := by
  rw [← sumL]
  have h := tendsto_multiset_sum (S n) (fun r hr => D_tendsto r (S_re_ne n hr))
  refine h.congr (fun Y => ?_)
  rw [two_arg n hn Y]

theorem countP_add (n : ℕ) :
    (S n).countP (fun r => 0 < r.re) + (S n).countP (fun r => ¬ 0 < r.re) = n + 1 := by
  rw [← card_S n, Multiset.card_eq_countP_add_countP (fun r : ℂ => 0 < r.re)]

/-! Quadrant of Q(iY) for Y > 1 and the count. -/

theorem count_Q (m : ℕ) :
    (1 ≤ m → (S (4 * m)).countP (fun r => 0 < r.re) = 2 * m) ∧
    (S (4 * m + 1)).countP (fun r => 0 < r.re) = 2 * m + 2 ∧
    (S (4 * m + 2)).countP (fun r => 0 < r.re) = 2 * m + 2 ∧
    (S (4 * m + 3)).countP (fun r => 0 < r.re) = 2 * m + 2 := by
  have hpi := Real.pi_pos
  -- From eventual bounds lo ≤ 2 arg Q(iY) ≤ hi to bounds on N_L - N_R.
  have bounds : ∀ n : ℕ, 1 ≤ n → ∀ lo hi : ℝ,
      (∀ Y : ℝ, 1 < Y → lo ≤ 2 * arg (Q n (I * Y)) ∧ 2 * arg (Q n (I * Y)) ≤ hi) →
      lo ≤ π * (((S n).countP (fun r => ¬ 0 < r.re) : ℝ) - ((S n).countP (fun r => 0 < r.re) : ℝ)) ∧
      π * (((S n).countP (fun r => ¬ 0 < r.re) : ℝ) - ((S n).countP (fun r => 0 < r.re) : ℝ)) ≤ hi := by
    intro n hn lo hi hb
    have hl := limit_eq n hn
    have ev : ∀ᶠ Y : ℝ in atTop, 1 < Y := eventually_gt_atTop 1
    exact ⟨ge_of_tendsto hl (ev.mono fun Y hY => (hb Y hY).1),
      le_of_tendsto hl (ev.mono fun Y hY => (hb Y hY).2)⟩
  refine ⟨fun hm => ?_, ?_, ?_, ?_⟩
  · have hb := bounds (4 * m) (by omega) π (2 * π) (fun Y hY => by
      have hre := (Q_re m Y).1
      have him := (Q_im m Y).1
      have p1 : 1 ≤ Y ^ (4 * m) := one_le_pow₀ hY.le
      have p2 : 0 < Y ^ (4 * m + 1) := by positivity
      have a1 : ¬ arg (Q (4 * m) (I * Y)) ≤ π / 2 := by
        rw [arg_le_pi_div_two_iff]
        push Not
        constructor <;> linarith
      have a2 := arg_le_pi (Q (4 * m) (I * Y))
      constructor <;> linarith)
    have hsum := countP_add (4 * m)
    set NR := (S (4 * m)).countP (fun r => 0 < r.re)
    set NL := (S (4 * m)).countP (fun r => ¬ 0 < r.re)
    have c1 : (1 : ℝ) ≤ (NL : ℝ) - NR := by nlinarith [hb.1]
    have c2 : (NL : ℝ) - NR ≤ 2 := by nlinarith [hb.2]
    have d1 : NR + 1 ≤ NL := by exact_mod_cast (by linarith : (NR : ℝ) + 1 ≤ NL)
    have d2 : NL ≤ NR + 2 := by exact_mod_cast (by linarith : (NL : ℝ) ≤ NR + 2)
    omega
  · have hb := bounds (4 * m + 1) (by omega) (-2 * π) (-π) (fun Y hY => by
      have hre := (Q_re m Y).2.1
      have him := (Q_im m Y).2.1
      have p1 : 1 < Y ^ (4 * m + 2) := one_lt_pow₀ hY (by omega)
      have p2 : 0 < Y ^ (4 * m + 1) := by positivity
      have a1 : ¬ -(π / 2) ≤ arg (Q (4 * m + 1) (I * Y)) := by
        rw [neg_pi_div_two_le_arg_iff]
        push Not
        constructor <;> linarith
      have a2 := neg_pi_lt_arg (Q (4 * m + 1) (I * Y))
      constructor <;> linarith)
    have hsum := countP_add (4 * m + 1)
    set NR := (S (4 * m + 1)).countP (fun r => 0 < r.re)
    set NL := (S (4 * m + 1)).countP (fun r => ¬ 0 < r.re)
    have c1 : (-2 : ℝ) ≤ (NL : ℝ) - NR := by nlinarith [hb.1]
    have c2 : (NL : ℝ) - NR ≤ -1 := by nlinarith [hb.2]
    have d1 : NR ≤ NL + 2 := by exact_mod_cast (by linarith : (NR : ℝ) ≤ NL + 2)
    have d2 : NL + 1 ≤ NR := by exact_mod_cast (by linarith : (NL : ℝ) + 1 ≤ NR)
    omega
  · have hb := bounds (4 * m + 2) (by omega) (-π) 0 (fun Y hY => by
      have hre := (Q_re m Y).2.2.1
      have him := (Q_im m Y).2.2.1
      have p1 : 0 < Y ^ (4 * m + 2) := by positivity
      have p2 : 0 < Y ^ (4 * m + 3) := by positivity
      have a1 : |arg (Q (4 * m + 2) (I * Y))| ≤ π / 2 := by
        rw [abs_arg_le_pi_div_two_iff]
        linarith
      have a2 : arg (Q (4 * m + 2) (I * Y)) < 0 := by
        rw [arg_neg_iff]
        linarith
      have a3 := neg_abs_le (arg (Q (4 * m + 2) (I * Y)))
      constructor <;> linarith)
    have hsum := countP_add (4 * m + 2)
    set NR := (S (4 * m + 2)).countP (fun r => 0 < r.re)
    set NL := (S (4 * m + 2)).countP (fun r => ¬ 0 < r.re)
    have c1 : (-1 : ℝ) ≤ (NL : ℝ) - NR := by nlinarith [hb.1]
    have c2 : (NL : ℝ) - NR ≤ 0 := by nlinarith [hb.2]
    have d1 : NR ≤ NL + 1 := by exact_mod_cast (by linarith : (NR : ℝ) ≤ NL + 1)
    have d2 : NL ≤ NR := by exact_mod_cast (by linarith : (NL : ℝ) ≤ NR)
    omega
  · have hb := bounds (4 * m + 3) (by omega) 0 π (fun Y hY => by
      have hre := (Q_re m Y).2.2.2
      have him := (Q_im m Y).2.2.2
      have p1 : 0 < Y ^ (4 * m + 4) := by positivity
      have p2 : 0 < Y ^ (4 * m + 3) := by positivity
      have a1 : |arg (Q (4 * m + 3) (I * Y))| ≤ π / 2 := by
        rw [abs_arg_le_pi_div_two_iff]
        linarith
      have a2 : 0 ≤ arg (Q (4 * m + 3) (I * Y)) := by
        rw [arg_nonneg_iff]
        linarith
      have a3 := le_abs_self (arg (Q (4 * m + 3) (I * Y)))
      constructor <;> linarith)
    have hsum := countP_add (4 * m + 3)
    set NR := (S (4 * m + 3)).countP (fun r => 0 < r.re)
    set NL := (S (4 * m + 3)).countP (fun r => ¬ 0 < r.re)
    have c1 : (0 : ℝ) ≤ (NL : ℝ) - NR := by nlinarith [hb.1]
    have c2 : (NL : ℝ) - NR ≤ 1 := by nlinarith [hb.2]
    have d1 : NR ≤ NL := by exact_mod_cast (by linarith : (NR : ℝ) ≤ NL)
    have d2 : NL ≤ NR + 1 := by exact_mod_cast (by linarith : (NL : ℝ) ≤ NR + 1)
    omega

/-! From Q = (X - 1) P to P. -/

theorem count_P_Q (n : ℕ) :
    (Pp n).roots.countP (fun r => 0 < r.re) + 1 = (S n).countP (fun r => 0 < r.re) := by
  have hQ : (X - C 1) * Pp n ≠ 0 := by
    rw [Qp_factor]
    exact (Qp_monic n).ne_zero
  unfold S
  rw [← Qp_factor, roots_mul hQ, roots_X_sub_C, Multiset.countP_add,
    show ({1} : Multiset ℂ) = 1 ::ₘ 0 from rfl, Multiset.countP_cons, Multiset.countP_zero]
  simp only [Complex.one_re, zero_lt_one, ↓reduceIte]
  omega

/-- The number of roots (with multiplicity) of x^n - x^(n-1) - ... - 1 with positive
real part is 1 + 2 floor((n-1)/4), for n ≥ 1. -/
theorem P_count (n : ℕ) (hn : 1 ≤ n) :
    (Pp n).roots.countP (fun r => 0 < r.re) = 1 + 2 * ((n - 1) / 4) := by
  have h := count_P_Q n
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hc := count_Q m
  interval_cases r
  · have hm : 1 ≤ m := by omega
    have := hc.1 hm
    simp only [Nat.add_zero] at h ⊢
    omega
  · have := hc.2.1
    omega
  · have := hc.2.2.1
    omega
  · have := hc.2.2.2
    omega

/-- A129756 by its closed form (entry name: odd numbers repeated four times). -/
def a (n : ℕ) : ℕ := 1 + 2 * (n / 4)

/-- Lagneau's conjecture, with the polynomial of degree n + 1: a(n) is the number of roots
of x^(n+1) - x^n - ... - x - 1 in the open right half-plane, counted with multiplicity. -/
theorem A129756_roots (n : ℕ) : (Pp (n + 1)).roots.countP (fun r => 0 < r.re) = a n := by
  rw [P_count (n + 1) (by omega)]
  unfold a
  simp

/-- Companion statement (A083219, a(n) = n - 2 floor(n/4)): the number of roots of
x^(n+1) - x^n - ... - x - 1 in the open left half-plane is n - 2 floor(n/4). -/
theorem A083219_roots (n : ℕ) :
    (Pp (n + 1)).roots.countP (fun r => r.re < 0) = n - 2 * (n / 4) := by
  have hQ : (X - C 1) * Pp (n + 1) ≠ 0 := by
    rw [Qp_factor]
    exact (Qp_monic (n + 1)).ne_zero
  have hroots : S (n + 1) = 1 ::ₘ (Pp (n + 1)).roots := by
    unfold S
    rw [← Qp_factor, roots_mul hQ, roots_X_sub_C]
    rfl
  have hcard : (Pp (n + 1)).roots.card = n + 1 := by
    have := card_S (n + 1)
    rw [hroots, Multiset.card_cons] at this
    omega
  have hre : ∀ r ∈ (Pp (n + 1)).roots, r.re ≠ 0 := fun r hr =>
    S_re_ne (n + 1) (by rw [hroots]; exact Multiset.mem_cons_of_mem hr)
  have hsplit := Multiset.card_eq_countP_add_countP (fun r : ℂ => 0 < r.re) (Pp (n + 1)).roots
  have hcong : (Pp (n + 1)).roots.countP (fun r => ¬ 0 < r.re) =
      (Pp (n + 1)).roots.countP (fun r => r.re < 0) := by
    apply Multiset.countP_congr rfl
    intro r hr
    have := hre r hr
    apply propext
    constructor
    · intro h
      exact lt_of_le_of_ne (not_lt.mp h) this
    · intro h
      exact not_lt.mpr h.le
  have hR := A129756_roots n
  unfold a at hR
  omega
