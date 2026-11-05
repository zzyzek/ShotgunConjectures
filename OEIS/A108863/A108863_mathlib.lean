/-
OEIS A108863, Mathlib proof of R. J. Mathar's conjecture "this is the Motzkin transform of the
sequence of three zeros followed by A001651".

Definitions.
* `A001006 n`: Motzkin numbers, M(0) = M(1) = 1, M(n+2) = M(n+1) + Σ_{k=0..n} M(k) M(n-k);
  `A108863_M` = Σ M(n) x^n, so M = 1 + x M + x^2 M^2 (`A108863_M_eq`).
* `A001651 m` (offset 1): the m-th positive integer not divisible by 3 (`Nat.nth`).
* `A108863_b k`: 0 for k < 3, A001651(k-2) for k ≥ 3 (three zeros followed by A001651).
* Motzkin transform (Mathar, A132894): substitute x -> x M(x) in the g.f.;
  `A108863_transform` = (Σ b_k x^k).subst (x M). `A108863_transform_coeff`: its n-th coefficient
  is Σ_{k=0..n} b_k [x^n] (x M)^k.
* A108863 itself (Dyck paths with exactly one UUUD) is represented by the entry's g.f.
  G = (x - 1 + (1-2x) M)/(x (1-3x)(1 + x M)), i.e. the unique power series with
  x (1-3x)(1 + x M) G = x - 1 + (1-2x) M.

Main theorem `A108863_conjecture`: x (1-3x)(1 + x M) · transform = x - 1 + (1-2x) M.
`A108863_unique`: any G with that equation equals the transform. So the transform is the
printed g.f. of A108863.

Proof. b has g.f. x^3 (1+x+x^2)/((1-x)(1-x^2)) (`A108863_B_eq`, from A001651(m) = ⌊(3m-1)/2⌋,
`A001651_eq`). Substitution is a ring homomorphism, so with y = x M:
transform · (1-y)(1-y^2) = y^3 (1+y+y^2). With y = x + x y + x y^2 the claimed equation times
x (1-y)^2 is a polynomial identity (quotient found by sympy, certificate/check.py), and
x (1-y)^2 ≠ 0 in the domain ℚ⟦x⟧.

Not checked in Lean: that the printed g.f. counts Dyck paths with exactly one UUUD
(certificate/check.py compares it with brute-force enumeration for n ≤ 11 and with the entry's terms),
and that the Motzkin numbers' combinatorial definition matches the recurrence used (standard).
-/
import Mathlib

open Finset PowerSeries

/-- Motzkin numbers A001006. -/
def A001006 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => A001006 (n + 1) + ∑ k ∈ (range (n + 1)).attach, A001006 k.1 * A001006 (n - k.1)
decreasing_by
  all_goals first
    | omega
    | (have := mem_range.mp k.2; omega)

/-- The Motzkin g.f. M(x). -/
noncomputable def A108863_M : ℚ⟦X⟧ := mk fun n => (A001006 n : ℚ)

theorem A108863_M_eq : A108863_M = 1 + X * A108863_M + X ^ 2 * A108863_M ^ 2 := by
  ext n
  rcases n with _ | _ | n
  · simp [A108863_M, A001006]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_X_pow_mul', ite_eq_right (by omega)]
    simp [A108863_M, A001006]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_X_pow_mul', ite_eq_left (by omega),
      show n + 2 - 2 = n by omega, pow_two, coeff_mul, coeff_one]
    simp only [A108863_M, coeff_mk]
    rw [A001006, Nat.cast_add, Nat.cast_sum, sum_attach (range (n + 1))
      (fun k => ((A001006 k * A001006 (n - k) : ℕ) : ℚ)),
      ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => ((A001006 i * A001006 j : ℕ) : ℚ))]
    push_cast
    simp

/-- A001651 (offset 1): the m-th positive integer not divisible by 3. -/
noncomputable def A001651 (m : ℕ) : ℕ := Nat.nth (fun x => ¬ 3 ∣ x) (m - 1)

theorem A001651_count (n : ℕ) : Nat.count (fun x => ¬ 3 ∣ x) n = n - (n + 2) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, ih]
    split_ifs with h <;> omega

theorem A001651_eq (m : ℕ) (hm : 1 ≤ m) : A001651 m = (3 * m - 1) / 2 := by
  unfold A001651
  have hp : ¬ 3 ∣ (3 * m - 1) / 2 := by omega
  have hc : Nat.count (fun x => ¬ 3 ∣ x) ((3 * m - 1) / 2) = m - 1 := by
    rw [A001651_count]; omega
  rw [← hc, Nat.nth_count hp]

/-- Three zeros followed by A001651. -/
noncomputable def A108863_b (k : ℕ) : ℕ := if k < 3 then 0 else A001651 (k - 2)

theorem A108863_b_eq (k : ℕ) : A108863_b k = if k < 3 then 0 else (3 * (k - 2) - 1) / 2 := by
  unfold A108863_b
  split_ifs with h
  · rfl
  · exact A001651_eq _ (by omega)

/-- g.f. of b. -/
noncomputable def A108863_B : ℚ⟦X⟧ := mk fun k => (A108863_b k : ℚ)

theorem A108863_B_eq :
    A108863_B * ((1 - X) * (1 - X ^ 2)) = X ^ 3 * (1 + X + X ^ 2) := by
  rw [show A108863_B * ((1 - X) * (1 - X ^ 2)) =
      A108863_B - A108863_B * X ^ 1 - A108863_B * X ^ 2 + A108863_B * X ^ 3 by ring,
    show (X : ℚ⟦X⟧) ^ 3 * (1 + X + X ^ 2) = X ^ 3 + X ^ 4 + X ^ 5 by ring]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow, A108863_B,
    coeff_mk, A108863_b_eq]
  rcases lt_or_ge n 6 with hn | hn
  · interval_cases n <;> norm_num
  · have c0 : ¬ n < 3 := by omega
    have c1 : ¬ n - 1 < 3 := by omega
    have c2 : ¬ n - 2 < 3 := by omega
    have c3 : ¬ n - 3 < 3 := by omega
    have d1 : 1 ≤ n := by omega
    have d2 : 2 ≤ n := by omega
    have d3 : 3 ≤ n := by omega
    have e3 : n ≠ 3 := by omega
    have e4 : n ≠ 4 := by omega
    have e5 : n ≠ 5 := by omega
    simp only [c0, c1, c2, c3, d1, d2, d3, e3, e4, e5, ↓reduceIte]
    obtain ⟨t, ht⟩ : ∃ t, n = 2 * t + 6 ∨ n = 2 * t + 7 := ⟨(n - 6) / 2, by omega⟩
    rcases ht with ht | ht
    · rw [show (3 * (n - 2) - 1) / 2 = 3 * t + 5 by omega, show (3 * (n - 1 - 2) - 1) / 2 = 3 * t + 4 by omega,
        show (3 * (n - 2 - 2) - 1) / 2 = 3 * t + 2 by omega, show (3 * (n - 3 - 2) - 1) / 2 = 3 * t + 1 by omega]
      push_cast
      ring
    · rw [show (3 * (n - 2) - 1) / 2 = 3 * t + 7 by omega, show (3 * (n - 1 - 2) - 1) / 2 = 3 * t + 5 by omega,
        show (3 * (n - 2 - 2) - 1) / 2 = 3 * t + 4 by omega, show (3 * (n - 3 - 2) - 1) / 2 = 3 * t + 2 by omega]
      push_cast
      ring

/-- x M(x). -/
noncomputable def A108863_y : ℚ⟦X⟧ := X * A108863_M

theorem A108863_hasSubst : HasSubst A108863_y :=
  HasSubst.of_constantCoeff_zero' (by simp [A108863_y])

/-- The Motzkin transform of b: substitute x -> x M(x) in the g.f. of b. -/
noncomputable def A108863_transform : ℚ⟦X⟧ := A108863_B.subst A108863_y

theorem A108863_transform_coeff (n : ℕ) :
    coeff n A108863_transform = ∑ k ∈ range (n + 1), (A108863_b k : ℚ) * coeff n (A108863_y ^ k) := by
  rw [A108863_transform, coeff_subst' A108863_hasSubst]
  rw [finsum_eq_sum_of_support_subset _ (s := range (n + 1))]
  · refine sum_congr rfl fun k _ => ?_
    simp [A108863_B, smul_eq_mul]
  · intro k hk
    rw [Function.mem_support] at hk
    rw [coe_range, Set.mem_Iio]
    by_contra h
    apply hk
    rw [A108863_y, mul_pow, coeff_X_pow_mul', ite_eq_right (by omega), smul_zero]

theorem A108863_transform_eq :
    A108863_transform * ((1 - A108863_y) * (1 - A108863_y ^ 2)) =
      A108863_y ^ 3 * (1 + A108863_y + A108863_y ^ 2) := by
  have h := congrArg (substAlgHom A108863_hasSubst) A108863_B_eq
  simp only [map_mul, map_sub, map_one, map_pow, map_add, substAlgHom_X] at h
  rw [coe_substAlgHom] at h
  exact h

theorem A108863_conjecture :
    X * (1 - 3 * X) * (1 + X * A108863_M) * A108863_transform = X - 1 + (1 - 2 * X) * A108863_M := by
  have hA := A108863_transform_eq
  have hM := A108863_M_eq
  unfold A108863_y at hA
  have hne : (X : ℚ⟦X⟧) * (1 - X * A108863_M) ^ 2 ≠ 0 := by
    refine mul_ne_zero X_ne_zero (pow_ne_zero 2 fun h0 => ?_)
    have := congrArg constantCoeff h0
    simp at this
  apply mul_left_cancel₀ hne
  set M := A108863_M
  set A := A108863_transform
  linear_combination (X ^ 2 * (1 - 3 * X)) * hA -
    X * (-3 * X ^ 2 * (X * M) ^ 3 + X * (X * M) ^ 3 - 3 * X * (X * M) ^ 2 + 3 * X * (X * M) - X +
      (X * M) ^ 2 - 2 * (X * M) + 1) * hM

theorem A108863_unique (G : ℚ⟦X⟧)
    (hG : X * (1 - 3 * X) * (1 + X * A108863_M) * G = X - 1 + (1 - 2 * X) * A108863_M) :
    G = A108863_transform := by
  have hne : (X : ℚ⟦X⟧) * (1 - 3 * X) * (1 + X * A108863_M) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero X_ne_zero fun h0 => ?_) fun h0 => ?_
    · have := congrArg constantCoeff h0
      simp at this
    · have := congrArg constantCoeff h0
      simp at this
  exact mul_left_cancel₀ hne (hG.trans A108863_conjecture.symm)
