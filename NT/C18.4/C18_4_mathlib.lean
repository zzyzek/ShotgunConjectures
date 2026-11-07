import Mathlib
import OpenProblemsLib.ModularSums

/-
Guy, UPINT C18 (Heden): on the n × n modular (toroidal) board, is the maximum number M(n) of
non-attacking queens equal to n - 2 when 3 | n or 4 | n? Known: P. Monsky, solution to E3162,
Amer. Math. Monthly 96 (1989) 258-259; explicit placements in K. Williams, arXiv:2404.18237,
proof of Thm 6.

Checked here (`queens_lower`): for every n ≥ 3 with 3 ∣ n or 4 ∣ n there is a set of n - 2
squares of ZMod n × ZMod n, pairwise distinct in x, in y, in x + y and in y - x (two queens on
the torus attack iff one of these agrees). The placements are Williams' five residue families
(n = 6m+3, 12m+4, 12m+6, 12m-4, 12m) plus explicit sets for n = 4, 6, 12.
Each family is checked for every m: for columns t1 < t2 the differences of y, x + y, y - x are
k·n only for |k| ≤ 6, and each k is excluded by `omega` on every pair of pieces.
Checked here (`queens_upper`): every non-attacking set has at most n - 2 queens (Monsky's
argument: the four coordinate maps of n - 1 queens each miss one value; sums and sums of squares,
in ZMod n when 3 ∣ n and of lifts in ZMod (2n) when 4 ∣ n, force n ∣ Σ_{i<n} i² or a variant,
which fails; `miss`, `sum_zmod`, `sq_lift` from library `OpenProblemsLib.ModularSums`). Main theorem `modular_queens_eq`: both statements, i.e. M(n) = n - 2.
Not checked: nothing beyond reading M(n) as the maximum size of such a set.
-/

namespace NT_C18_4

open OpenProblemsLib.ModularSums

/-- Pairwise non-attacking queens on the n × n torus. -/
def NonAttacking {n : ℕ} (S : Finset (ZMod n × ZMod n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p.1 + p.2 ≠ q.1 + q.2 ∧ p.2 - p.1 ≠ q.2 - q.1

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

theorem family_to_finset (n : ℕ) (Y : ℤ → ℤ) (e1 e2 : ℕ) (he : e1 ≠ e2) (he1 : e1 < n)
    (he2 : e2 < n)
    (hok : ∀ t1 t2 : ℕ, t1 < t2 → t2 < n → t1 ≠ e1 → t1 ≠ e2 → t2 ≠ e1 → t2 ≠ e2 →
      ∀ j : ℤ, (j = -1 ∨ j = 0 ∨ j = 1) → ¬ (n : ℤ) ∣ (Y t2 + j * t2) - (Y t1 + j * t1)) :
    ∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S := by
  classical
  set T : Finset ℕ := (Finset.range n) \ {e1, e2} with hT
  have hTc : T.card = n - 2 := by
    rw [hT, Finset.card_sdiff_of_subset (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa using ‹_›)]
    simp [Finset.card_pair he]
  have hmemT : ∀ t, t ∈ T ↔ t < n ∧ t ≠ e1 ∧ t ≠ e2 := by
    intro t; simp [hT]
  have cast_inj : ∀ a b : ℕ, a < n → b < n → ((a : ZMod n) = b) → a = b := by
    intro a b ha hb h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  -- an ordered key: for t1 < t2 in T, the three keys differ in ZMod n
  have key : ∀ t1 t2 : ℕ, t1 ∈ T → t2 ∈ T → t1 < t2 → ∀ j : ℤ, (j = -1 ∨ j = 0 ∨ j = 1) →
      ((Y t1 + j * t1 : ℤ) : ZMod n) ≠ ((Y t2 + j * t2 : ℤ) : ZMod n) := by
    intro t1 t2 h1 h2 hlt j hj heq
    rw [hmemT] at h1 h2
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
    exact hok t1 t2 hlt h2.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 j hj heq
  refine ⟨T.image (fun t : ℕ => ((t : ZMod n), ((Y (t : ℤ) : ℤ) : ZMod n))), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hTc]
    intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    exact cast_inj a b ((hmemT a).1 ha).1 ((hmemT b).1 hb).1 hab.1
  · intro p hp q hq hpq
    simp only [Finset.mem_image] at hp hq
    obtain ⟨t1, h1, rfl⟩ := hp
    obtain ⟨t2, h2, rfl⟩ := hq
    have hne : t1 ≠ t2 := by rintro rfl; exact hpq rfl
    have k0 := fun a b (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) => key a b ha hb hab 0 (by simp)
    have kp := fun a b (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) => key a b ha hb hab 1 (by simp)
    have km := fun a b (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) => key a b ha hb hab (-1) (by simp)
    simp only [zero_mul, add_zero, one_mul, neg_one_mul, ← sub_eq_add_neg] at k0 kp km
    push_cast at k0 kp km
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hne (cast_inj t1 t2 ((hmemT t1).1 h1).1 ((hmemT t2).1 h2).1 h)
    · intro h
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact k0 t1 t2 h1 h2 hl h
      · exact k0 t2 t1 h2 h1 hl h.symm
    · intro h
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact kp t1 t2 h1 h2 hl (by simpa [add_comm] using h)
      · exact kp t2 t1 h2 h1 hl (by simpa [add_comm] using h.symm)
    · intro h
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact km t1 t2 h1 h2 hl h
      · exact km t2 t1 h2 h1 hl h.symm

theorem lower_F3 (m : ℕ) :
    ∃ S : Finset (ZMod (6*m+3) × ZMod (6*m+3)), S.card = (6*m+3) - 2 ∧ NonAttacking S :=
  family_to_finset (6*m+3) (YF3 m) (3*m+1) (4*m+2) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F3_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F4 (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset (ZMod (12*m+4) × ZMod (12*m+4)), S.card = (12*m+4) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m+4) (YF4 m) (5*m) (12*m+3) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F4_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F6 (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset (ZMod (12*m+6) × ZMod (12*m+6)), S.card = (12*m+6) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m+6) (YF6 m) (6*m+3) (8*m+4) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F6_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F8 (m : ℕ) :
    ∃ S : Finset (ZMod (12*m+8) × ZMod (12*m+8)), S.card = (12*m+8) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m+8) (YF8 ((m : ℤ) + 1)) (2*m+1) (9*m+5) (by omega) (by omega) (by omega)
    (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F8_ok ((m : ℤ) + 1) t1 t2 j k (by omega) hj (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F12 (m : ℕ) (hm : 2 ≤ m) :
    ∃ S : Finset (ZMod (12*m) × ZMod (12*m)), S.card = (12*m) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m) (YF12 m) (4*m-2) (9*m-1) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F12_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_4 : ∃ S : Finset (ZMod 4 × ZMod 4), S.card = 4 - 2 ∧ NonAttacking S :=
  ⟨{(0, 0), (1, 2)}, by decide, by unfold NonAttacking; decide⟩

theorem lower_6 : ∃ S : Finset (ZMod 6 × ZMod 6), S.card = 6 - 2 ∧ NonAttacking S :=
  ⟨{(0, 0), (1, 3), (2, 5), (3, 2)}, by decide, by unfold NonAttacking; decide⟩

theorem lower_12 : ∃ S : Finset (ZMod 12 × ZMod 12), S.card = 12 - 2 ∧ NonAttacking S :=
  ⟨{(0, 0), (1, 2), (2, 4), (3, 1), (4, 7), (5, 9), (6, 11), (7, 3), (8, 5), (11, 10)},
    by decide +kernel, by unfold NonAttacking; decide +kernel⟩

/-- Heden's conjectured lower bound: n - 2 non-attacking queens on the n × n torus whenever
3 ∣ n or 4 ∣ n (n ≥ 3). -/
theorem queens_lower (n : ℕ) (h3 : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n) :
    ∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S := by
  have hr : n % 12 = 0 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 6 ∨ n % 12 = 8 ∨ n % 12 = 9 := by
    omega
  rcases hr with h | h | h | h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m := ⟨n / 12, by omega⟩
    rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
    · exact lower_12
    · exact lower_F12 m hm
  · obtain ⟨m, rfl⟩ : ∃ m, n = 6 * m + 3 := ⟨n / 6, by omega⟩
    exact lower_F3 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m + 4 := ⟨n / 12, by omega⟩
    rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
    · exact lower_4
    · exact lower_F4 m hm
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m + 6 := ⟨n / 12, by omega⟩
    rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
    · exact lower_6
    · exact lower_F6 m hm
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m + 8 := ⟨n / 12, by omega⟩
    exact lower_F8 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 6 * m + 3 := ⟨n / 6, by omega⟩
    exact lower_F3 m

/-! Upper bound (Monsky): no n - 1 non-attacking queens when 3 ∣ n or 4 ∣ n. -/

theorem six_sum_sq (N : ℕ) : 6 * ∑ i ∈ Finset.range (N + 1), i ^ 2 = N * (N + 1) * (2 * N + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem no_n_minus_one (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n)
    (S : Finset (ZMod n × ZMod n)) (hS : NonAttacking S) (hc : S.card + 1 = n) : False := by
  classical
  have : NeZero n := ⟨by omega⟩
  have inj : ∀ (f : ZMod n × ZMod n → ZMod n), (∀ p ∈ S, ∀ q ∈ S, p ≠ q → f p ≠ f q) →
      Set.InjOn f S := by
    intro f hf p hp q hq hpq
    by_contra hne; exact hf p hp q hq hne hpq
  obtain ⟨a, ha⟩ := miss S (fun p => p.1) (inj _ fun p hp q hq h => (hS p hp q hq h).1) hc
  obtain ⟨b, hb⟩ := miss S (fun p => p.2) (inj _ fun p hp q hq h => (hS p hp q hq h).2.1) hc
  obtain ⟨c, hc'⟩ := miss S (fun p => p.1 + p.2)
    (inj _ fun p hp q hq h => (hS p hp q hq h).2.2.1) hc
  obtain ⟨d, hd'⟩ := miss S (fun p => p.2 - p.1)
    (inj _ fun p hp q hq h => (hS p hp q hq h).2.2.2) hc
  set T : ZMod n := ∑ v, v with hTdef
  have hT : T + T = 0 := by
    have : T = -T := by
      rw [hTdef, ← Finset.sum_neg_distrib]
      exact (Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun v => by simp)).symm
    calc T + T = T + -T := by rw [← this]
      _ = 0 := add_neg_cancel T
  -- linear relations between the missing values
  have l1 := ha (fun v => v); have l2 := hb (fun v => v)
  have l3 := hc' (fun v => v); have l4 := hd' (fun v => v)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at l1 l2 l3 l4
  have hcab : c = a + b - T := by rw [l1, l2] at l3; linear_combination l3
  have hdab : d = T - a + b := by rw [l1, l2] at l4; linear_combination l4
  rcases hd with h3 | h4
  · -- squares in ZMod n
    have s1 := ha (fun v => v ^ 2); have s2 := hb (fun v => v ^ 2)
    have s3 := hc' (fun v => v ^ 2); have s4 := hd' (fun v => v ^ 2)
    have par : ∑ p ∈ S, (p.1 + p.2) ^ 2 + ∑ p ∈ S, (p.2 - p.1) ^ 2 =
        2 * ∑ p ∈ S, p.1 ^ 2 + 2 * ∑ p ∈ S, p.2 ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [s1, s2, s3, s4, hcab, hdab] at par
    have hQ : 2 * ∑ v : ZMod n, v ^ 2 = 0 := by
      linear_combination -par - (T - 2 * a) * hT
    rw [sum_zmod (fun v : ZMod n => v ^ 2)] at hQ
    have hcast : (2 * ∑ i ∈ Finset.range n, (i : ZMod n) ^ 2) =
        ((2 * ∑ i ∈ Finset.range n, i ^ 2 : ℕ) : ZMod n) := by push_cast; rfl
    rw [hcast, ZMod.natCast_eq_zero_iff] at hQ
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    obtain ⟨j, hj⟩ := hQ
    have h6 := six_sum_sq N
    have : (N + 1) * (3 * j) = (N + 1) * (N * (2 * N + 1)) := by
      have : 3 * (2 * ∑ i ∈ Finset.range (N + 1), i ^ 2) = 3 * ((N + 1) * j) := by rw [hj]
      nlinarith
    have h3j := Nat.eq_of_mul_eq_mul_left (by omega) this
    have hN : N % 3 = 2 := by omega
    have : (N * (2 * N + 1)) % 3 = 1 := by
      rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod 2, hN]
    omega
  · -- squares of lifts in ZMod (2n)
    have h2 : 2 ∣ n := dvd_trans ⟨2, rfl⟩ h4
    let L : ZMod n → ZMod (2 * n) := fun v => ((v.val : ℤ) : ZMod (2 * n))
    have Lsq : ∀ (v : ZMod n) (w : ℤ), (w : ZMod n) = v → L v ^ 2 = (w : ZMod (2 * n)) ^ 2 := by
      intro v w h
      exact sq_lift h2 _ _ (by rw [h]; simp)
    have s1 := ha (fun v => L v ^ 2); have s2 := hb (fun v => L v ^ 2)
    have s3 := hc' (fun v => L v ^ 2); have s4 := hd' (fun v => L v ^ 2)
    have par : ∑ p ∈ S, L (p.1 + p.2) ^ 2 + ∑ p ∈ S, L (p.2 - p.1) ^ 2 =
        2 * ∑ p ∈ S, L p.1 ^ 2 + 2 * ∑ p ∈ S, L p.2 ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Lsq (p.1 + p.2) ((p.1.val : ℤ) + p.2.val) (by push_cast; simp),
        Lsq (p.2 - p.1) ((p.2.val : ℤ) - p.1.val) (by push_cast; simp)]
      simp only [L]; push_cast; ring
    have hc2 : L c ^ 2 = (L a + L b - L T) ^ 2 := by
      rw [Lsq c ((a.val : ℤ) + b.val - T.val) (by push_cast; simp [hcab])]
      simp only [L]; push_cast; ring
    have hd2 : L d ^ 2 = (L T - L a + L b) ^ 2 := by
      rw [Lsq d ((T.val : ℤ) - a.val + b.val) (by push_cast; simp [hdab])]
      simp only [L]; push_cast; ring
    rw [s1, s2, s3, s4, hc2, hd2] at par
    -- T.val is 0 or n/2
    obtain ⟨k, rfl⟩ := h4
    have hk0 : 1 ≤ k := by omega
    have hTv : T.val = 0 ∨ T.val = 2 * k := by
      have h0 : ((2 * T.val : ℕ) : ZMod (4 * k)) = 0 := by
        push_cast; rw [ZMod.natCast_zmod_val]; linear_combination hT
      rw [ZMod.natCast_eq_zero_iff] at h0
      obtain ⟨j, hj⟩ := h0
      have hlt : T.val < 4 * k := ZMod.val_lt T
      have hj2 : j < 2 := by nlinarith
      interval_cases j <;> omega
    have hQ : 2 * ∑ v : ZMod (4 * k), L v ^ 2 = 0 := by
      have h0 : ((2 * (4 * k) : ℕ) : ZMod (2 * (4 * k))) = 0 := ZMod.natCast_self _
      rcases hTv with ht | ht
      · have hLT : L T = 0 := by simp only [L]; rw [ht]; simp
        rw [hLT] at par; linear_combination -par
      · have hLT : L T = ((2 * k : ℕ) : ZMod (2 * (4 * k))) := by simp only [L]; rw [ht]; simp
        rw [hLT] at par
        have e : (2 : ZMod (2 * (4 * k))) * ((2 * k : ℕ) : ZMod (2 * (4 * k))) ^ 2 -
            4 * L a * ((2 * k : ℕ) : ZMod (2 * (4 * k))) =
            ((2 * (4 * k) : ℕ) : ZMod (2 * (4 * k))) * (k - L a) := by push_cast; ring
        rw [h0, zero_mul] at e
        linear_combination -par - e
    rw [sum_zmod (fun v : ZMod (4 * k) => L v ^ 2)] at hQ
    have hL : ∀ i ∈ Finset.range (4 * k), L (i : ZMod (4 * k)) ^ 2 = ((i ^ 2 : ℕ) : ZMod (2 * (4 * k))) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [L]; rw [ZMod.val_cast_of_lt hi]; push_cast; ring
    rw [Finset.sum_congr rfl hL] at hQ
    have hcast : (2 * ∑ i ∈ Finset.range (4 * k), ((i ^ 2 : ℕ) : ZMod (2 * (4 * k)))) =
        ((2 * ∑ i ∈ Finset.range (4 * k), i ^ 2 : ℕ) : ZMod (2 * (4 * k))) := by push_cast; rfl
    rw [hcast, ZMod.natCast_eq_zero_iff] at hQ
    obtain ⟨j, hj⟩ := hQ
    obtain ⟨N, hN⟩ : ∃ N, 4 * k = N + 1 := ⟨4 * k - 1, by omega⟩
    have h6 := six_sum_sq N
    rw [hN] at hj
    have : (N + 1) * (6 * j) = (N + 1) * (N * (2 * N + 1)) := by nlinarith
    have h6j := Nat.eq_of_mul_eq_mul_left (by omega) this
    have hN2 : N % 2 = 1 := by omega
    have : (N * (2 * N + 1)) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod 2, hN2]
    omega

/-- Monsky's upper bound: at most n - 2 non-attacking queens on the n × n torus when 3 ∣ n or
4 ∣ n. -/
theorem queens_upper (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n)
    (S : Finset (ZMod n × ZMod n)) (hS : NonAttacking S) : S.card ≤ n - 2 := by
  by_contra h
  obtain ⟨S', hsub, hcard⟩ := Finset.exists_subset_card_eq (show n - 1 ≤ S.card by omega)
  exact no_n_minus_one n hn hd S' (fun p hp q hq => hS p (hsub hp) q (hsub hq)) (by omega)

/-- M(n) = n - 2 when 3 ∣ n or 4 ∣ n: n - 2 non-attacking queens exist and no larger set does. -/
theorem modular_queens_eq (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n) :
    (∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S) ∧
    ∀ S : Finset (ZMod n × ZMod n), NonAttacking S → S.card ≤ n - 2 :=
  ⟨queens_lower n hn hd, fun S hS => queens_upper n hn hd S hS⟩
