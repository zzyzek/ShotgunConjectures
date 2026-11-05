/-
OEIS A025191, Mathlib proof of the conjectures
  a(n) = A027914(n) - A027914(n-1) = (A081673(n) - A081673(n-1))/2   (n ≥ 1).

Definitions, as in the entries.
* `A025191_tri n k` = A027907(n, k) = [x^k] (1 + x + x^2)^n (trinomial coefficients).
* `A025177 n k` = A027907(n, k) - A027907(n-1, k-1) (first differences in the n,n direction;
  the second term is 0 for n = 0 or k = 0). Its g.f. is (1 - yz)/(1 - z(1 + y + y^2)).
* `A025191 n` = Σ_{k=0..n} A025177(n, k).
* `A027914 n` = Σ_{k=0..n} A027907(n, k).
* `A081673 n` = n! [x^n] (exp(3x) - exp(x)(1 - I0)), where I0 is the power series
  Σ_j x^(2j)/(j!)^2, i.e. BesselI_0(2x) (the entry's e.g.f.).

Main theorem `A025191_conjecture`: for n ≥ 1,
  A025191 n = A027914 n - A027914 (n-1)  and  A025191 n = (A081673 n - A081673 (n-1))/2.
Supporting: `A025191_tri_symm` (row symmetry, via `Polynomial.reflect`), `A025191_two_A027914`
(2 A027914(n) = 3^n + A027907(n, n)), `A025191_central` (A027907(n, n) = Σ_{m even} C(n,m) C(m,m/2)),
`A081673_formula` (A081673(n) = 3^n - 1 + Σ_{m even} C(n,m) C(m,m/2)), `A081673_eq`
(A081673(n) = 2 A027914(n) - 1).

Not checked in Lean: that BesselI_0(2x) = Σ_j x^(2j)/(j!)^2 (the textbook series of I_0).
The first OEIS terms of every sequence are checked against these definitions in
certificate/check.py, not in Lean (the polynomial coefficients are noncomputable).
-/
import Mathlib

open Polynomial Finset

/-- A027907(n, k) = [x^k] (1 + x + x^2)^n. -/
noncomputable def A025191_tri (n k : ℕ) : ℕ := ((1 + X + X ^ 2 : ℕ[X]) ^ n).coeff k

/-- A025177(n, k) = A027907(n, k) - A027907(n-1, k-1). -/
noncomputable def A025177 (n k : ℕ) : ℤ :=
  (A025191_tri n k : ℤ) - (if n = 0 ∨ k = 0 then 0 else (A025191_tri (n - 1) (k - 1) : ℤ))

/-- A025191(n) = Σ_{k=0..n} A025177(n, k). -/
noncomputable def A025191 (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), A025177 n k

/-- A027914(n) = Σ_{k=0..n} A027907(n, k). -/
noncomputable def A027914 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), A025191_tri n k

/-- BesselI_0(2x) = Σ_j x^(2j)/(j!)^2. -/
noncomputable def A081673_I0 : PowerSeries ℚ :=
  PowerSeries.mk fun m => if Even m then 1 / ((m / 2).factorial : ℚ) ^ 2 else 0

/-- exp(3x) - exp(x) (1 - BesselI_0(2x)). -/
noncomputable def A081673_egf : PowerSeries ℚ :=
  PowerSeries.rescale 3 (PowerSeries.exp ℚ) - PowerSeries.exp ℚ * (1 - A081673_I0)

/-- A081673(n) = n! [x^n] e.g.f. -/
noncomputable def A081673 (n : ℕ) : ℚ := n.factorial * PowerSeries.coeff n A081673_egf

theorem A025191_eq_diff (n : ℕ) (hn : 1 ≤ n) :
    A025191 n = (A027914 n : ℤ) - A027914 (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold A025191 A027914 A025177
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [sum_sub_distrib, sum_range_succ' _ (m + 1)]
  simp only [false_or]
  rw [sum_range_succ' (fun x => if x = 0 then (0 : ℤ) else (A025191_tri m (x - 1) : ℤ))]
  simp

theorem A025191_natDegree_le (n : ℕ) : ((1 + X + X ^ 2 : ℕ[X]) ^ n).natDegree ≤ 2 * n := by
  refine natDegree_pow_le.trans ?_
  have h : (1 + X + X ^ 2 : ℕ[X]).natDegree ≤ 2 := by compute_degree
  nlinarith

theorem A025191_reflect (n : ℕ) :
    reflect (2 * n) ((1 + X + X ^ 2 : ℕ[X]) ^ n) = (1 + X + X ^ 2) ^ n := by
  induction n with
  | zero => simp [reflect_one]
  | succ n ih =>
    have h2 : (1 + X + X ^ 2 : ℕ[X]).natDegree ≤ 2 := by compute_degree
    rw [pow_succ, show 2 * (n + 1) = 2 * n + 2 by ring,
      reflect_mul _ _ (A025191_natDegree_le n) h2, ih]
    congr 1
    have e1 : reflect 2 (X : ℕ[X]) = X := by
      rw [← pow_one X, reflect_monomial, revAt_le (by norm_num)]
    have e2 : reflect 2 (X ^ 2 : ℕ[X]) = 1 := by
      rw [reflect_monomial, revAt_le (by norm_num)]
      simp
    rw [reflect_add, reflect_add, reflect_one, e1, e2]
    ring

theorem A025191_tri_symm (n k : ℕ) (hk : k ≤ 2 * n) : A025191_tri n k = A025191_tri n (2 * n - k) := by
  unfold A025191_tri
  conv_lhs => rw [← A025191_reflect n]
  rw [coeff_reflect, revAt_le hk]

theorem A025191_row_sum (n : ℕ) : ∑ k ∈ range (2 * n + 1), A025191_tri n k = 3 ^ n := by
  have h := eval_eq_sum_range' (p := (1 + X + X ^ 2 : ℕ[X]) ^ n)
    (Nat.lt_succ_of_le (A025191_natDegree_le n)) 1
  simp only [one_pow, mul_one, eval_pow, eval_add, eval_one, eval_X] at h
  unfold A025191_tri
  rw [← h]
  norm_num

theorem A025191_two_A027914 (n : ℕ) : 2 * A027914 n = 3 ^ n + A025191_tri n n := by
  rw [← A025191_row_sum, show 2 * n + 1 = (n + 1) + n by ring, sum_range_add]
  have hs : ∑ j ∈ range n, A025191_tri n (n + 1 + j) = ∑ j ∈ range n, A025191_tri n (n - 1 - j) := by
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [A025191_tri_symm n (n + 1 + j) (by omega)]
    congr 1
    omega
  rw [hs, sum_range_reflect (fun j => A025191_tri n j) n]
  unfold A027914
  rw [sum_range_succ]
  ring

theorem A025191_coeff_one_add_X_sq (m : ℕ) :
    ((1 + X ^ 2 : ℕ[X]) ^ m).coeff m = if Even m then m.choose (m / 2) else 0 := by
  rw [add_comm, add_pow, finsetSum_coeff]
  simp only [one_pow, mul_one, ← pow_mul, coeff_mul_natCast, coeff_X_pow]
  split_ifs with he
  · obtain ⟨j, rfl⟩ := he
    rw [sum_eq_single j]
    · simp [show j + j = 2 * j by ring]
    · intro b _ hb
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      simp
    · intro hj
      exact absurd (mem_range.mpr (by omega)) hj
  · refine sum_eq_zero fun i _ => ?_
    rw [ite_eq_right_iff.mpr (fun h => absurd ⟨i, by omega⟩ he)]
    simp

theorem A025191_central (n : ℕ) :
    A025191_tri n n = ∑ m ∈ range (n + 1), if Even m then n.choose m * m.choose (m / 2) else 0 := by
  unfold A025191_tri
  rw [show (1 + X + X ^ 2 : ℕ[X]) = (1 + X ^ 2) + X by ring, add_pow, finsetSum_coeff]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  rw [coeff_mul_natCast, coeff_mul_X_pow', ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
    show n - (n - m) = m by omega, A025191_coeff_one_add_X_sq]
  simp only [Nat.cast_id]
  split_ifs <;> ring

theorem A081673_term (n k : ℕ) (hk : k ≤ n) (he : Even k) :
    (n.factorial : ℚ) * (1 / ((n - k).factorial : ℚ) * (1 / ((k / 2).factorial : ℚ) ^ 2)) =
      (n.choose k * k.choose (k / 2) : ℕ) := by
  obtain ⟨j, rfl⟩ := he
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have h2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + j by omega)
  rw [show (j + j) / 2 = j by omega]
  rw [show j + j - j = j by omega] at h2
  rw [← h1, ← h2]
  push_cast
  field_simp

theorem A081673_coeff (n : ℕ) :
    PowerSeries.coeff n A081673_egf = 3 ^ n * (1 / (n.factorial : ℚ)) - 1 / (n.factorial : ℚ) +
      ∑ m ∈ range (n + 1), 1 / ((n - m).factorial : ℚ) *
        (if Even m then 1 / ((m / 2).factorial : ℚ) ^ 2 else 0) := by
  unfold A081673_egf
  rw [mul_sub, mul_one, map_sub, map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.swap_prod_mk, PowerSeries.coeff_exp, A081673_I0, PowerSeries.coeff_mk,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem A081673_formula (n : ℕ) :
    A081673 n = 3 ^ n - 1 +
      ∑ m ∈ range (n + 1), ((if Even m then n.choose m * m.choose (m / 2) else 0 : ℕ) : ℚ) := by
  unfold A081673
  rw [A081673_coeff, mul_add, mul_sub, mul_sum]
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  congr 1
  · field_simp
  · refine sum_congr rfl fun m hm => ?_
    rw [mem_range] at hm
    split_ifs with he
    · exact A081673_term n m (by omega) he
    · simp

theorem A081673_eq (n : ℕ) : A081673 n = 2 * (A027914 n : ℚ) - 1 := by
  rw [A081673_formula, ← Nat.cast_sum, ← A025191_central]
  have h := A025191_two_A027914 n
  have h' : (2 : ℚ) * (A027914 n : ℚ) = 3 ^ n + (A025191_tri n n : ℚ) := by exact_mod_cast h
  linarith

theorem A025191_conjecture (n : ℕ) (hn : 1 ≤ n) :
    A025191 n = (A027914 n : ℤ) - A027914 (n - 1) ∧
      (A025191 n : ℚ) = (A081673 n - A081673 (n - 1)) / 2 := by
  refine ⟨A025191_eq_diff n hn, ?_⟩
  rw [A025191_eq_diff n hn, A081673_eq, A081673_eq]
  push_cast
  ring
