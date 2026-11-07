import Mathlib

/-!
# OEIS A215010: an equiangular 10-gon with sides in arithmetic progression

The entry conjectures that hexagons are the only simple convex equiangular polygons whose integer side
lengths form an arithmetic progression t, t+d, ..., t+(n-1)d (in some order). An equiangular n-gon with
consecutive sides L_0, ..., L_(n-1) closes iff sum_k L_k w^k = 0, w = exp(2 pi i/n).

Main results.
* `A215010_offsets_perm` : the offsets m = (0,6,2,8,4,5,1,7,3,9) are a permutation of 0..9.
* `A215010_closes` : for every primitive 10th root of unity w and all t, d,
  sum_k (t + m_k d) w^k = 0.
* `A215010_closes_exp` : the same for w = exp(2 pi i / 10).

Checked: the closing condition. Not checked: that a closed polygon with positive sides whose edge
directions turn by 2 pi / 10 at each vertex is simple and convex (standard).
-/

open Complex

def offs : Fin 10 → ℕ := ![0, 6, 2, 8, 4, 5, 1, 7, 3, 9]

theorem A215010_offsets_perm : (List.ofFn offs).Perm (List.range 10) := by decide

theorem A215010_closes (w : ℂ) (hw : IsPrimitiveRoot w 10) (t d : ℂ) :
    ∑ k : Fin 10, (t + (offs k : ℂ) * d) * w ^ (k : ℕ) = 0 := by
  have h10 : w ^ 10 = 1 := hw.pow_eq_one
  have h5ne : w ^ 5 ≠ 1 := hw.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h5 : w ^ 5 = -1 := by
    have : (w ^ 5) * (w ^ 5) = 1 := by rw [← pow_add]; exact h10
    rcases mul_self_eq_one_iff.mp this with h | h
    · exact absurd h h5ne
    · exact h
  have h2ne : w ^ 2 ≠ 1 := hw.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hw1 : 1 + w ≠ 0 := by
    intro h
    have : w = -1 := by linear_combination h
    apply h2ne; rw [this]; norm_num
  have hphi : 1 - w + w ^ 2 - w ^ 3 + w ^ 4 = 0 := by
    have : (1 + w) * (1 - w + w ^ 2 - w ^ 3 + w ^ 4) = 0 := by linear_combination h5
    exact (mul_eq_zero.mp this).resolve_left hw1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, offs]
  simp
  linear_combination ((t + 5 * d) + (t + d) * w + (t + 7 * d) * w ^ 2 + (t + 3 * d) * w ^ 3 +
    (t + 9 * d) * w ^ 4) * h5 + (-5 * d) * hphi

theorem A215010_closes_exp (t d : ℂ) :
    ∑ k : Fin 10, (t + (offs k : ℂ) * d) * (exp (2 * Real.pi * I / 10)) ^ (k : ℕ) = 0 := by
  have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  push_cast at this
  exact A215010_closes _ this t d
