
def YF3 (m t : ℤ) : ℤ := if t < m then 2*t else if t < 3*m+1 then 2*t + 1 else if t < 4*m+2 then 2*t else 2*t - 1

theorem YF3_close (m t : ℤ) : 2*t - 4 ≤ YF3 m t ∧ YF3 m t ≤ 2*t + 3 := by
  unfold YF3; split_ifs <;> omega

theorem F3_j0_k0 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (-6) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k1 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (-5) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k2 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (-4) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k3 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (-3) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k4 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (-2) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k5 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (-1) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k6 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (0) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k7 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (1) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k8 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (2) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k9 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (3) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k10 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (4) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k11 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (5) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j0_k12 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + (-1) * t2) - (YF3 m t1 + (-1) * t1) = (6) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k0 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (-6) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k1 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (-5) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k2 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (-4) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k3 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (-3) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k4 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (-2) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k5 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (-1) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k6 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (0) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k7 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (1) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k8 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (2) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k9 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (3) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k10 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (4) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k11 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (5) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j1_k12 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 0 * t2) - (YF3 m t1 + 0 * t1) = (6) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k0 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (-6) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k1 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (-5) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k2 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (-4) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k3 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (-3) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k4 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (-2) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k5 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (-1) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k6 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (0) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k7 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (1) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k8 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (2) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k9 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (3) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k10 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (4) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k11 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (5) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_j2_k12 (m t1 t2 : ℤ) (hm : 0 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + 1 * t2) - (YF3 m t1 + 1 * t1) = (6) * (6*m+3)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF3 at hk; split_ifs at hk <;> intros <;> omega

theorem F3_ok (m t1 t2 j k : ℤ) (hm : 0 ≤ m) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 6*m+3)
    (a1 : t1 ≠ 3*m+1) (a2 : t1 ≠ 4*m+2) (b1 : t2 ≠ 3*m+1) (b2 : t2 ≠ 4*m+2)
    (hk : (YF3 m t2 + j * t2) - (YF3 m t1 + j * t1) = k * (6*m+3)) : False := by
  have c1 := YF3_close m t1
  have c2 := YF3_close m t2
  have hkl : -7 < k := by rcases hj with rfl | rfl | rfl <;> nlinarith
  have hku : k < 7 := by rcases hj with rfl | rfl | rfl <;> nlinarith
  rcases hj with rfl | rfl | rfl
  · interval_cases k
    · exact F3_j0_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j0_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F3_j1_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j1_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F3_j2_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F3_j2_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk

def YF4 (m t : ℤ) : ℤ := if t < 2*m then 3*t else if t < 5*m then 3*t + 2 else if t < 6*m+2 then 3*t else if t < 9*m+2 then 3*t + 1 else 3*t + 3

theorem YF4_close (m t : ℤ) : 3*t - 4 ≤ YF4 m t ∧ YF4 m t ≤ 3*t + 3 := by
  unfold YF4; split_ifs <;> omega

theorem F4_j0_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (-6) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (-5) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (-4) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (-3) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (-2) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (-1) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (0) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (1) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (2) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (3) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (4) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (5) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j0_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + (-1) * t2) - (YF4 m t1 + (-1) * t1) = (6) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (-6) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (-5) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (-4) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (-3) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (-2) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (-1) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (0) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (1) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (2) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (3) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (4) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (5) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j1_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 0 * t2) - (YF4 m t1 + 0 * t1) = (6) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (-6) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (-5) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (-4) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (-3) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (-2) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (-1) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (0) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (1) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (2) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (3) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (4) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (5) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_j2_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + 1 * t2) - (YF4 m t1 + 1 * t1) = (6) * (12*m+4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF4 at hk; split_ifs at hk <;> intros <;> omega

theorem F4_ok (m t1 t2 j k : ℤ) (hm : 1 ≤ m) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+4)
    (a1 : t1 ≠ 5*m) (a2 : t1 ≠ 12*m+3) (b1 : t2 ≠ 5*m) (b2 : t2 ≠ 12*m+3)
    (hk : (YF4 m t2 + j * t2) - (YF4 m t1 + j * t1) = k * (12*m+4)) : False := by
  have c1 := YF4_close m t1
  have c2 := YF4_close m t2
  have hkl : -7 < k := by rcases hj with rfl | rfl | rfl <;> nlinarith
  have hku : k < 7 := by rcases hj with rfl | rfl | rfl <;> nlinarith
  rcases hj with rfl | rfl | rfl
  · interval_cases k
    · exact F4_j0_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j0_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F4_j1_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j1_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F4_j2_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F4_j2_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk

def YF6 (m t : ℤ) : ℤ := if t < 2*m then 3*t else if t < 6*m+2 then 3*t + 1 else if t < 6*m+3 then 3*t else if t < 8*m+4 then 3*t - 3 else 3*t - 4

theorem YF6_close (m t : ℤ) : 3*t - 4 ≤ YF6 m t ∧ YF6 m t ≤ 3*t + 3 := by
  unfold YF6; split_ifs <;> omega

theorem F6_j0_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (-6) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (-5) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (-4) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (-3) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (-2) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (-1) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (0) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (1) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (2) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (3) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (4) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (5) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j0_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + (-1) * t2) - (YF6 m t1 + (-1) * t1) = (6) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (-6) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (-5) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (-4) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (-3) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (-2) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (-1) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (0) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (1) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (2) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (3) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (4) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (5) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j1_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 0 * t2) - (YF6 m t1 + 0 * t1) = (6) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (-6) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (-5) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (-4) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (-3) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (-2) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (-1) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (0) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (1) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (2) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (3) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (4) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (5) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_j2_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + 1 * t2) - (YF6 m t1 + 1 * t1) = (6) * (12*m+6)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF6 at hk; split_ifs at hk <;> intros <;> omega

theorem F6_ok (m t1 t2 j k : ℤ) (hm : 1 ≤ m) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m+6)
    (a1 : t1 ≠ 6*m+3) (a2 : t1 ≠ 8*m+4) (b1 : t2 ≠ 6*m+3) (b2 : t2 ≠ 8*m+4)
    (hk : (YF6 m t2 + j * t2) - (YF6 m t1 + j * t1) = k * (12*m+6)) : False := by
  have c1 := YF6_close m t1
  have c2 := YF6_close m t2
  have hkl : -7 < k := by rcases hj with rfl | rfl | rfl <;> nlinarith
  have hku : k < 7 := by rcases hj with rfl | rfl | rfl <;> nlinarith
  rcases hj with rfl | rfl | rfl
  · interval_cases k
    · exact F6_j0_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j0_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F6_j1_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j1_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F6_j2_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F6_j2_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk

def YF8 (m t : ℤ) : ℤ := if t < 2*m-1 then 3*t else if t < 5*m-2 then 3*t - 2 else if t < 6*m-2 then 3*t else if t < 9*m-4 then 3*t - 1 else 3*t - 3

theorem YF8_close (m t : ℤ) : 3*t - 4 ≤ YF8 m t ∧ YF8 m t ≤ 3*t + 3 := by
  unfold YF8; split_ifs <;> omega

theorem F8_j0_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (-6) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (-5) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (-4) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (-3) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (-2) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (-1) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (0) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (1) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (2) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (3) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (4) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (5) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j0_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + (-1) * t2) - (YF8 m t1 + (-1) * t1) = (6) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (-6) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (-5) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (-4) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (-3) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (-2) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (-1) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (0) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (1) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (2) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (3) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (4) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (5) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j1_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 0 * t2) - (YF8 m t1 + 0 * t1) = (6) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k0 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (-6) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k1 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (-5) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k2 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (-4) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k3 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (-3) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k4 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (-2) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k5 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (-1) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k6 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (0) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k7 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (1) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k8 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (2) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k9 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (3) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k10 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (4) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k11 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (5) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_j2_k12 (m t1 t2 : ℤ) (hm : 1 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + 1 * t2) - (YF8 m t1 + 1 * t1) = (6) * (12*m-4)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF8 at hk; split_ifs at hk <;> intros <;> omega

theorem F8_ok (m t1 t2 j k : ℤ) (hm : 1 ≤ m) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m-4)
    (a1 : t1 ≠ 2*m-1) (a2 : t1 ≠ 9*m-4) (b1 : t2 ≠ 2*m-1) (b2 : t2 ≠ 9*m-4)
    (hk : (YF8 m t2 + j * t2) - (YF8 m t1 + j * t1) = k * (12*m-4)) : False := by
  have c1 := YF8_close m t1
  have c2 := YF8_close m t2
  have hkl : -7 < k := by rcases hj with rfl | rfl | rfl <;> nlinarith
  have hku : k < 7 := by rcases hj with rfl | rfl | rfl <;> nlinarith
  rcases hj with rfl | rfl | rfl
  · interval_cases k
    · exact F8_j0_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j0_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F8_j1_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j1_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F8_j2_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F8_j2_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk

def YF12 (m t : ℤ) : ℤ := if t < 3*m-1 then 3*t else if t < 4*m-2 then 3*t + 3 else if t < 6*m-1 then 3*t + 2 else if t < 9*m-1 then 3*t + 1 else if t < 10*m then 3*t - 2 else 3*t - 1

theorem YF12_close (m t : ℤ) : 3*t - 4 ≤ YF12 m t ∧ YF12 m t ≤ 3*t + 3 := by
  unfold YF12; split_ifs <;> omega

theorem F12_j0_k0 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (-6) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k1 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (-5) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k2 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (-4) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k3 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (-3) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k4 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (-2) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k5 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (-1) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k6 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (0) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k7 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (1) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k8 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (2) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k9 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (3) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k10 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (4) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k11 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (5) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j0_k12 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + (-1) * t2) - (YF12 m t1 + (-1) * t1) = (6) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k0 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (-6) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k1 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (-5) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k2 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (-4) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k3 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (-3) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k4 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (-2) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k5 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (-1) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k6 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (0) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k7 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (1) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k8 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (2) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k9 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (3) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k10 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (4) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k11 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (5) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j1_k12 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 0 * t2) - (YF12 m t1 + 0 * t1) = (6) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k0 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (-6) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k1 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (-5) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k2 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (-4) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k3 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (-3) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k4 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (-2) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k5 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (-1) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k6 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (0) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k7 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (1) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k8 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (2) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k9 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (3) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k10 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (4) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k11 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (5) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_j2_k12 (m t1 t2 : ℤ) (hm : 2 ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + 1 * t2) - (YF12 m t1 + 1 * t1) = (6) * (12*m)) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold YF12 at hk; split_ifs at hk <;> intros <;> omega

theorem F12_ok (m t1 t2 j k : ℤ) (hm : 2 ≤ m) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < 12*m)
    (a1 : t1 ≠ 4*m-2) (a2 : t1 ≠ 9*m-1) (b1 : t2 ≠ 4*m-2) (b2 : t2 ≠ 9*m-1)
    (hk : (YF12 m t2 + j * t2) - (YF12 m t1 + j * t1) = k * (12*m)) : False := by
  have c1 := YF12_close m t1
  have c2 := YF12_close m t2
  have hkl : -7 < k := by rcases hj with rfl | rfl | rfl <;> nlinarith
  have hku : k < 7 := by rcases hj with rfl | rfl | rfl <;> nlinarith
  rcases hj with rfl | rfl | rfl
  · interval_cases k
    · exact F12_j0_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j0_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F12_j1_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j1_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
  · interval_cases k
    · exact F12_j2_k0 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k1 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k2 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k3 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k4 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k5 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k6 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k7 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k8 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k9 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k10 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k11 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
    · exact F12_j2_k12 m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk
