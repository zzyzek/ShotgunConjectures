/-
BMP 1.8.7 (Moser): f(d) = maximum number of congruent regular d-simplices of
edge 1 that pack into the unit d-cube. Lower bound f(d) >= m^d with
m = Nat.sqrt ((d+1)/4), hence log f(d) / d >= log m -> infinity.

Construction. n = d+1, cas x = cos x + sin x. The vertex k (0 <= k <= d) is
  v_k(t) = cas (2 pi k (t+1) / n) / sqrt (2 n),   t = 0..d-1.
The Hartley identity sum_{t<n} (cas a_t - cas b_t)^2 = 2n (from the vanishing
of sums of n-th roots of unity) gives dist v_k v_l = 1 for k /= l, and
|cas| <= sqrt 2 gives every coordinate in [-1/sqrt n, 1/sqrt n]. Copies are
translated on a grid of step s = 2/sqrt n, indexed by g : Fin d -> Fin m.

Checked by Lean (Mathlib only):
  * regular_simplex_in_small_box: an edge-1 regular simplex in R^d with all
    coordinates of absolute value at most 1/sqrt(d+1), whose convex hull
    has nonempty interior (the vertices are affinely independent, from the
    orthogonality of the n x n Hartley matrix).
  * moser_pack: the m^d translated copies (indexed by Fin d -> Fin m) have
    all vertices in [0,1]^d, each convex hull has nonempty interior, and
    the interiors are pairwise disjoint (interior taken in
    EuclideanSpace R (Fin d)). So the copies are pairwise distinct.
  * moser_tendsto: Nat.sqrt ((d+1)/4) -> infinity.
  * moser_log_tendsto: log (m^d) / d -> infinity.
Not checked: the definition of f(d) itself (maximum over all packings) is not
formalised, so "f(d) >= m^d" is the reading of moser_pack, not a Lean
statement. The statements hold for every d (d = 0 included, trivially), so
no hypothesis 1 <= d is used.
-/
import Mathlib

open Real Finset Filter

namespace BMP187

noncomputable section

/-- Hartley kernel. -/
def cas (x : ℝ) : ℝ := Real.cos x + Real.sin x

/-- The angle 2 pi m t / n. -/
def ang (n : ℕ) (m : ℤ) (t : ℕ) : ℝ := 2 * π * m * t / n

lemma trig_sums (n : ℕ) (hn : 0 < n) (m : ℤ) :
    (∑ t ∈ range n, Real.sin (ang n m t) = 0) ∧
    (¬ (n : ℤ) ∣ m → ∑ t ∈ range n, Real.cos (ang n m t) = 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set z : ℂ := Complex.exp (2 * π * m / n * Complex.I) with hzdef
  have hz : ∀ t : ℕ, z ^ t = Complex.exp ((ang n m t : ℝ) * Complex.I) := by
    intro t
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    simp only [ang]
    push_cast
    ring
  have hzn : z ^ n = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul]
    have e : (n : ℂ) * (2 * π * m / n * Complex.I) = (m : ℂ) * (2 * π * Complex.I) := by
      field_simp
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  have hsin : ∑ t ∈ range n, Real.sin (ang n m t) = (∑ t ∈ range n, z ^ t).im := by
    rw [Complex.im_sum]
    simp [hz, Complex.exp_ofReal_mul_I_im]
  have hcos : ∑ t ∈ range n, Real.cos (ang n m t) = (∑ t ∈ range n, z ^ t).re := by
    rw [Complex.re_sum]
    simp [hz, Complex.exp_ofReal_mul_I_re]
  by_cases h1 : z = 1
  · refine ⟨?_, ?_⟩
    · rw [hsin, h1]
      simp
    · intro hnd
      exfalso
      apply hnd
      rw [hzdef, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have hm : (m : ℂ) = n * k := by
        have e : (m : ℂ) = (2 * π * m / n * Complex.I) * (n / (2 * π * Complex.I)) := by
          field_simp
        rw [e, hk]
        field_simp
      exact ⟨k, by exact_mod_cast hm⟩
  · have h0 : ∑ t ∈ range n, z ^ t = 0 := by
      rw [geom_sum_eq h1 n, hzn]
      simp
    exact ⟨by rw [hsin, h0]; simp, fun _ => by rw [hcos, h0]; simp⟩

lemma cas_sq_diff (a b : ℝ) :
    (cas a - cas b) ^ 2 =
      2 + Real.sin (2 * a) + Real.sin (2 * b) - 2 * Real.cos (a - b) - 2 * Real.sin (a + b) := by
  simp only [cas]
  rw [Real.sin_two_mul, Real.sin_two_mul, Real.cos_sub, Real.sin_add]
  linear_combination Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq b

lemma cas_sq_le (x : ℝ) : cas x ^ 2 ≤ 2 := by
  simp only [cas]
  nlinarith [sq_nonneg (Real.cos x - Real.sin x), Real.sin_sq_add_cos_sq x]

/-- Hartley identity: distinct columns are at squared distance 2n. -/
lemma hartley_sum (n k l : ℕ) (hk : k < n) (hl : l < n) (hkl : k ≠ l) :
    ∑ t ∈ range n, (cas (ang n k t) - cas (ang n l t)) ^ 2 = 2 * n := by
  have hn : 0 < n := by omega
  have e : ∀ t ∈ range n, (cas (ang n k t) - cas (ang n l t)) ^ 2 =
      2 + Real.sin (ang n (2 * k) t) + Real.sin (ang n (2 * l) t)
        - 2 * Real.cos (ang n ((k : ℤ) - l) t) - 2 * Real.sin (ang n ((k : ℤ) + l) t) := by
    intro t _
    rw [cas_sq_diff]
    simp only [ang]
    push_cast
    ring_nf
  have hnd : ¬ (n : ℤ) ∣ ((k : ℤ) - l) := by
    intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  rw [sum_congr rfl e]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [(trig_sums n hn _).1, (trig_sums n hn _).1, (trig_sums n hn _).2 hnd,
    (trig_sums n hn _).1]
  ring

/-- The simplex vertices. -/
def vert (d : ℕ) (k : Fin (d + 1)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun t : Fin d =>
    cas (ang (d + 1) (k : ℕ) ((t : ℕ) + 1)) / √(2 * ((d + 1 : ℕ) : ℝ)))

lemma vert_apply (d : ℕ) (k : Fin (d + 1)) (t : Fin d) :
    vert d k t = cas (ang (d + 1) (k : ℕ) ((t : ℕ) + 1)) / √(2 * ((d + 1 : ℕ) : ℝ)) := rfl

lemma vert_dist (d : ℕ) (k l : Fin (d + 1)) (hkl : k ≠ l) : dist (vert d k) (vert d l) = 1 := by
  have hpos : (0 : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by positivity
  have hc : (√(2 * ((d + 1 : ℕ) : ℝ))) ^ 2 = 2 * ((d + 1 : ℕ) : ℝ) := Real.sq_sqrt hpos.le
  set g : ℕ → ℝ := fun t => (cas (ang (d + 1) (k : ℕ) t) - cas (ang (d + 1) (l : ℕ) t)) ^ 2
    with hg
  have hS := hartley_sum (d + 1) k l k.isLt l.isLt (fun h => hkl (Fin.ext h))
  rw [sum_range_succ'] at hS
  have h0 : g 0 = 0 := by simp [hg, ang]
  have hsum : ∑ t : Fin d, g ((t : ℕ) + 1) = 2 * ((d + 1 : ℕ) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun t => g (t + 1)) d]
    have : ∑ t ∈ range d, g (t + 1) + g 0 = 2 * ((d + 1 : ℕ) : ℝ) := hS
    linarith
  rw [EuclideanSpace.dist_eq]
  have e : ∀ t : Fin d, dist (vert d k t) (vert d l t) ^ 2 =
      g ((t : ℕ) + 1) / (2 * ((d + 1 : ℕ) : ℝ)) := by
    intro t
    rw [Real.dist_eq, sq_abs, vert_apply, vert_apply, ← sub_div, div_pow, hc]
  simp only [e]
  rw [← sum_div, hsum, div_self hpos.ne', Real.sqrt_one]

lemma vert_bound (d : ℕ) (k : Fin (d + 1)) (t : Fin d) :
    |vert d k t| ≤ 1 / √((d : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hc : (√(2 * ((d + 1 : ℕ) : ℝ))) ^ 2 = 2 * ((d : ℝ) + 1) := by
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rw [one_div, ← Real.sqrt_inv]
  apply Real.abs_le_sqrt
  rw [vert_apply, div_pow, hc, div_le_iff₀ (by positivity)]
  have := cas_sq_le (ang (d + 1) (k : ℕ) ((t : ℕ) + 1))
  field_simp
  linarith

/-- Hartley orthogonality: the columns of the n x n Hartley matrix. -/
lemma hartley_inner (n k l : ℕ) (hk : k < n) (hl : l < n) :
    ∑ t ∈ range n, cas (ang n k t) * cas (ang n l t) = if k = l then (n : ℝ) else 0 := by
  have hn : 0 < n := by omega
  have e : ∀ t ∈ range n, cas (ang n k t) * cas (ang n l t) =
      Real.cos (ang n ((k : ℤ) - l) t) + Real.sin (ang n ((k : ℤ) + l) t) := by
    intro t _
    have h1 : ang n ((k : ℤ) - l) t = ang n k t - ang n l t := by
      simp only [ang]
      push_cast
      ring
    have h2 : ang n ((k : ℤ) + l) t = ang n k t + ang n l t := by
      simp only [ang]
      push_cast
      ring
    rw [h1, h2, Real.cos_sub, Real.sin_add]
    simp only [cas]
    ring
  rw [sum_congr rfl e, sum_add_distrib, (trig_sums n hn _).1, add_zero]
  split_ifs with h
  · subst h
    simp [ang]
  · have hnd : ¬ (n : ℤ) ∣ ((k : ℤ) - l) := by
      intro hd
      have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
      omega
    exact (trig_sums n hn _).2 hnd

/-- Every translate of the vertex family is affinely independent. -/
lemma vert_affineIndependent (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) :
    AffineIndependent ℝ (fun i => vert d i + c) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv l
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw c,
    Finset.weightedVSubOfPoint_apply] at hv
  simp only [vsub_eq_sub, add_sub_cancel_right] at hv
  have hcpos : 0 < √(2 * ((d + 1 : ℕ) : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hcol : ∀ t ∈ range (d + 1),
      ∑ k : Fin (d + 1), w k * cas (ang (d + 1) (k : ℕ) t) = 0 := by
    intro t ht
    rcases t with _ | t
    · simp [ang, cas, hw]
    · have ht' : t < d := by
        simp only [mem_range] at ht
        omega
      have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x ⟨t, ht'⟩) hv
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
        PiLp.zero_apply, vert_apply] at h1
      have h2 : (∑ k : Fin (d + 1), w k * cas (ang (d + 1) (k : ℕ) (t + 1))) /
          √(2 * ((d + 1 : ℕ) : ℝ)) = 0 := by
        rw [sum_div]
        rw [← h1]
        refine sum_congr rfl (fun k _ => ?_)
        ring
      rcases div_eq_zero_iff.1 h2 with h | h
      · exact h
      · exact absurd h hcpos.ne'
  have key : ((d + 1 : ℕ) : ℝ) * w l = 0 := by
    calc ((d + 1 : ℕ) : ℝ) * w l
        = ∑ k : Fin (d + 1), w k * (if (k : ℕ) = (l : ℕ) then ((d + 1 : ℕ) : ℝ) else 0) := by
          simp [Fin.val_inj, mul_comm]
      _ = ∑ k : Fin (d + 1), w k * ∑ t ∈ range (d + 1),
            cas (ang (d + 1) (k : ℕ) t) * cas (ang (d + 1) (l : ℕ) t) := by
          refine sum_congr rfl (fun k _ => ?_)
          rw [hartley_inner (d + 1) k l k.isLt l.isLt]
      _ = ∑ t ∈ range (d + 1), cas (ang (d + 1) (l : ℕ) t) *
            ∑ k : Fin (d + 1), w k * cas (ang (d + 1) (k : ℕ) t) := by
          simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl (fun t _ => sum_congr rfl (fun k _ => ?_))
          ring
      _ = 0 := by
          refine sum_eq_zero (fun t ht => ?_)
          rw [hcol t ht, mul_zero]
  have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h hn
  · exact h

/-- Every translated copy is a full-dimensional simplex. -/
lemma vert_interior_nonempty (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) :
    (interior (convexHull ℝ (Set.range fun i => vert d i + c))).Nonempty := by
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top,
    (vert_affineIndependent d c).affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp

theorem regular_simplex_in_small_box (d : ℕ) :
    ∃ v : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i j, i ≠ j → dist (v i) (v j) = 1) ∧
      (∀ i j', |v i j'| ≤ 1 / √((d : ℝ) + 1)) ∧
      (interior (convexHull ℝ (Set.range v))).Nonempty :=
  ⟨vert d, vert_dist d, vert_bound d, by simpa using vert_interior_nonempty d 0⟩

/-- A coordinate hyperplane has empty interior. -/
lemma interior_coord_eq_empty {d : ℕ} (j : Fin d) (c : ℝ)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : ∀ x ∈ S, x j = c) : interior S = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hball⟩ := hx
  have hy : x + (ε / 2) • PiLp.single 2 j (1 : ℝ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      PiLp.norm_single]
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    norm_num
    linarith
  have h1 := hS _ (hball hy)
  have h2 := hS _ (hball (Metric.mem_ball_self hε))
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
    smul_eq_mul, mul_one] at h1
  linarith

/-- Closed grid box g * s + [0, s]^d. -/
def box (d m : ℕ) (s : ℝ) (g : Fin d → Fin m) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, ((g j : ℕ) : ℝ) * s ≤ x j ∧ x j ≤ (((g j : ℕ) : ℝ) + 1) * s}

lemma box_convex (d m : ℕ) (s : ℝ) (g : Fin d → Fin m) : Convex ℝ (box d m s g) := by
  intro x hx y hy a b ha hb hab j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨hx1, hx2⟩ := hx j
  obtain ⟨hy1, hy2⟩ := hy j
  have e1 : ((g j : ℕ) : ℝ) * s = a * (((g j : ℕ) : ℝ) * s) + b * (((g j : ℕ) : ℝ) * s) := by
    rw [← add_mul, hab, one_mul]
  have e2 : (((g j : ℕ) : ℝ) + 1) * s =
      a * ((((g j : ℕ) : ℝ) + 1) * s) + b * ((((g j : ℕ) : ℝ) + 1) * s) := by
    rw [← add_mul, hab, one_mul]
  constructor
  · linarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
  · linarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]

/-- Translation of the copy with grid index g. -/
def tr (d m : ℕ) (g : Fin d → Fin m) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j : Fin d =>
    ((g j : ℕ) : ℝ) * (2 * (1 / √((d : ℝ) + 1))) + 1 / √((d : ℝ) + 1))

lemma vert_tr_mem_box (d m : ℕ) (g : Fin d → Fin m) (i : Fin (d + 1)) :
    vert d i + tr d m g ∈ box d m (2 * (1 / √((d : ℝ) + 1))) g := by
  intro j
  have hb := abs_le.1 (vert_bound d i j)
  simp only [PiLp.add_apply, tr]
  constructor <;> nlinarith [hb.1, hb.2]

lemma hull_sub_box (d m : ℕ) (g : Fin d → Fin m) :
    convexHull ℝ (Set.range fun i => vert d i + tr d m g) ⊆
      box d m (2 * (1 / √((d : ℝ) + 1))) g :=
  convexHull_min (Set.range_subset_iff.2 (vert_tr_mem_box d m g)) (box_convex d m _ g)

lemma two_m_le (d : ℕ) : 2 * ((Nat.sqrt ((d + 1) / 4) : ℕ) : ℝ) ≤ √((d : ℝ) + 1) := by
  have h1 := Nat.sqrt_le ((d + 1) / 4)
  have h2 := Nat.div_mul_le_self (d + 1) 4
  have h3 : (2 * Nat.sqrt ((d + 1) / 4)) ^ 2 ≤ d + 1 := by nlinarith
  have h4 : (2 * ((Nat.sqrt ((d + 1) / 4) : ℕ) : ℝ)) ^ 2 ≤ (d : ℝ) + 1 := by
    exact_mod_cast h3
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h4)

theorem moser_pack (d : ℕ) :
    ∃ (v : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
      (t : (Fin d → Fin (Nat.sqrt ((d + 1) / 4))) → EuclideanSpace ℝ (Fin d)),
      (∀ i j, i ≠ j → dist (v i) (v j) = 1) ∧
      (∀ g i j, 0 ≤ (v i + t g) j ∧ (v i + t g) j ≤ 1) ∧
      (∀ g, (interior (convexHull ℝ (Set.range fun i => v i + t g))).Nonempty) ∧
      (∀ g h, g ≠ h →
        Disjoint (interior (convexHull ℝ (Set.range fun i => v i + t g)))
          (interior (convexHull ℝ (Set.range fun i => v i + t h)))) := by
  set m := Nat.sqrt ((d + 1) / 4) with hm
  have hsq : 0 < √((d : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  set r := 1 / √((d : ℝ) + 1) with hr
  have hr0 : 0 < r := by positivity
  have hmr : (m : ℝ) * (2 * r) ≤ 1 := by
    have := two_m_le d
    rw [← hm] at this
    rw [hr, ← mul_assoc, mul_one_div, div_le_one hsq]
    linarith
  refine ⟨vert d, tr d m, vert_dist d, ?_, fun g => vert_interior_nonempty d (tr d m g), ?_⟩
  · intro g i j
    obtain ⟨h1, h2⟩ := vert_tr_mem_box d m g i j
    have hg : ((g j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast (g j).isLt
    have hg0 : (0 : ℝ) ≤ ((g j : ℕ) : ℝ) := by positivity
    constructor
    · nlinarith
    · nlinarith
  · intro g h hgh
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hgh
    rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter]
    apply Set.eq_empty_of_subset_empty
    refine le_trans (interior_mono (Set.inter_subset_inter (hull_sub_box d m g)
      (hull_sub_box d m h))) ?_
    rcases lt_or_gt_of_ne hj with hlt | hlt
    · rw [interior_coord_eq_empty j ((((g j : ℕ) : ℝ) + 1) * (2 * r))]
      rintro x ⟨hxg, hxh⟩
      have e : ((g j : ℕ) : ℝ) + 1 ≤ ((h j : ℕ) : ℝ) := by exact_mod_cast hlt
      have a := hxg j
      have b := hxh j
      nlinarith
    · rw [interior_coord_eq_empty j ((((h j : ℕ) : ℝ) + 1) * (2 * r))]
      rintro x ⟨hxg, hxh⟩
      have e : ((h j : ℕ) : ℝ) + 1 ≤ ((g j : ℕ) : ℝ) := by exact_mod_cast hlt
      have a := hxg j
      have b := hxh j
      nlinarith

theorem moser_tendsto : Tendsto (fun d : ℕ => Nat.sqrt ((d + 1) / 4)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨4 * b * b, fun a ha => ?_⟩
  rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by norm_num)]
  linarith

theorem moser_log_tendsto :
    Tendsto (fun d : ℕ => Real.log (((Nat.sqrt ((d + 1) / 4) : ℕ) : ℝ) ^ d) / d) atTop atTop := by
  have h := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp moser_tendsto)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hd' : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  simp only [Function.comp_apply, Real.log_pow]
  field_simp

end

end BMP187

open BMP187
