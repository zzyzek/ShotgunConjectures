/-
OEIS A088617, Mathlib proof.

T(n,k) = C(n+k,n) C(n,k)/(k+1) (the entry's definition, `T` below, natural
division as in the entry; the division is exact, `T_cast`).
r(n) = sum_k T(n,k) (large Schroeder numbers A006318) and
U(n) = sum_k k T(n,k) (total number of U steps over all Schroeder n-paths).
Callan's conjecture: the mean U(n)/r(n) is asymptotic to sqrt(1/2) n.

Main theorem `A088617_conjecture`: U(n)/r(n)/n -> sqrt(1/2).
Exact formula `A088617_total`: 4 U(n+1) = (3n+2) r(n+1) - n r(n).

Proof. f k n = (n+k)(n+k-1)...(n-k+1) (2k factors, a polynomial in n) gives
T(n,k) = f k n / (k! (k+1)!) for all n, k (`T_eq`), and the coefficient
identity (n+3) T(n+2,k+1) = (2n+3)(T(n+1,k+1) + 2 T(n+1,k)) - n T(n,k+1)
(`T_rec`) is a polynomial identity. Summing it with weights 1 and k gives
three-term recurrences for r and U (`r_rec`, `U_rec`), and induction gives
the exact formula. With x(n) = r(n+1)/r(n), the recurrence for r gives
(n+3) x(n+1) = 3(2n+3) - n/x(n), and induction gives
2 <= x(n) <= 3+2 sqrt 2 and (n+1)(3+2 sqrt 2 - x(n)) <= 20 (`x_bounds`), so
x(n) -> 3+2 sqrt 2, and U(n+1)/r(n+1) = ((3n+2) - n/x(n))/4 gives the limit
(3 - (3 - 2 sqrt 2))/4 = sqrt(1/2).

Checked: everything above, for T as defined by the entry's formula.
Not checked in Lean: that T(n,k) counts Schroeder n-paths with k U steps
(the entry's comment; classical).
-/
import Mathlib

open Filter Topology Finset

namespace A088617

/-- T(n,k) = C(n+k,n) C(n,k)/(k+1), the entry's definition. -/
def T (n k : ℕ) : ℕ := (n + k).choose n * n.choose k / (k + 1)

/-- r(n) = sum_k T(n,k), the number of Schroeder n-paths. -/
noncomputable def r (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), (T n k : ℝ)

/-- U(n) = sum_k k T(n,k), the total number of U steps. -/
noncomputable def U (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), (k : ℝ) * T n k

/-- f k n = (n+k)(n+k-1)...(n-k+1). -/
def f : ℕ → ℤ → ℤ
  | 0, _ => 1
  | k + 1, n => (n + k + 1) * (n - k) * f k n

theorem f_succ (k : ℕ) (n : ℤ) : f (k + 1) n = (n + k + 1) * (n - k) * f k n := rfl

theorem f_shift (k : ℕ) (n : ℤ) : f (k + 1) (n + 1) = (n + k + 2) * (n + k + 1) * f k n := by
  induction k with
  | zero =>
    rw [f_succ]
    simp only [f]
    push_cast
    ring
  | succ k ih =>
    rw [f_succ, ih, f_succ]
    push_cast
    ring

theorem f_eq_zero (k n : ℕ) (h : n < k) : f k (n : ℤ) = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [f_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [ih h', mul_zero]
    · subst h'
      ring

theorem f_fact (k : ℕ) : ∀ m : ℕ,
    f k ((k + m : ℕ) : ℤ) * (m.factorial : ℤ) = ((2 * k + m).factorial : ℤ) := by
  induction k with
  | zero => intro m; simp [f]
  | succ k ih =>
    intro m
    have h := ih (m + 1)
    rw [show k + 1 + m = k + (m + 1) by ring, f_succ,
      show 2 * (k + 1) + m = (2 * k + (m + 1)) + 1 by ring, Nat.factorial_succ (2 * k + (m + 1))]
    rw [Nat.factorial_succ] at h
    push_cast at h ⊢
    linear_combination (2 * (k : ℤ) + m + 2) * h

theorem T_zero_of_lt (n k : ℕ) (h : n < k) : T n k = 0 := by
  simp [T, Nat.choose_eq_zero_of_lt h]

theorem T_n_zero (n : ℕ) : T n 0 = 1 := by
  simp [T]

theorem T_cast (n k : ℕ) (h : k ≤ n) :
    (T n k : ℝ) * (k + 1) = ((n + k).choose n * n.choose k : ℕ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  have hP : (k + m + k).choose (k + m) * (k + m).choose k =
      (2 * k + m).choose (2 * k) * Nat.centralBinom k := by
    apply Nat.eq_of_mul_eq_mul_right
      (show 0 < k.factorial * k.factorial * m.factorial by positivity)
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k + m ≤ k + m + k by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + m by omega)
    have h3 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * k + m by omega)
    have h4 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show k + m + k - (k + m) = k by omega] at h1
    rw [show k + m - k = m by omega] at h2
    rw [show 2 * k + m - 2 * k = m by omega] at h3
    rw [show 2 * k - k = k by omega] at h4
    rw [Nat.centralBinom_eq_two_mul_choose]
    rw [show k + m + k = 2 * k + m by ring] at h1 ⊢
    calc (2 * k + m).choose (k + m) * (k + m).choose k * (k.factorial * k.factorial * m.factorial)
        = (2 * k + m).choose (k + m) * ((k + m).choose k * k.factorial * m.factorial) *
            k.factorial := by ring
      _ = (2 * k + m).factorial := by rw [h2, h1]
      _ = (2 * k + m).choose (2 * k) * ((2 * k).choose k * k.factorial * k.factorial) *
            m.factorial := by rw [h4, h3]
      _ = _ := by ring
  have hdvd : k + 1 ∣ (k + m + k).choose (k + m) * (k + m).choose k := by
    rw [hP]
    exact Dvd.dvd.mul_left (Nat.succ_dvd_centralBinom k) _
  unfold T
  rw [Nat.cast_div hdvd (by positivity)]
  push_cast
  field_simp

theorem T_eq (n k : ℕ) :
    (T n k : ℝ) = (f k n : ℝ) / ((k.factorial : ℝ) * (k + 1).factorial) := by
  rcases lt_or_ge n k with h | h
  · rw [T_zero_of_lt n k h, f_eq_zero k n h]
    simp
  have hc := T_cast n k h
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  have hf := f_fact k m
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k + m ≤ k + m + k by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + m by omega)
  rw [show k + m + k - (k + m) = k by omega, show k + m + k = 2 * k + m by ring] at h1
  rw [show k + m - k = m by omega] at h2
  rw [show k + m + k = 2 * k + m by ring] at hc
  have hfR : (f k ((k + m : ℕ) : ℤ) : ℝ) * (m.factorial : ℝ) = ((2 * k + m).factorial : ℝ) := by
    exact_mod_cast hf
  have hPR : (((2 * k + m).choose (k + m) * (k + m).choose k : ℕ) : ℝ) *
      ((k.factorial : ℝ) * k.factorial * m.factorial) = ((2 * k + m).factorial : ℝ) := by
    rw [← h1, ← h2]
    push_cast
    ring
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  have key : ((T (k + m) k : ℝ) * (k + 1) * (k.factorial * k.factorial) -
      (f k ((k + m : ℕ) : ℤ) : ℝ)) * m.factorial = 0 := by
    rw [hc]
    linear_combination hPR - hfR
  rcases mul_eq_zero.mp key with h0 | h0
  · push_cast at h0
    linear_combination h0
  · exact absurd h0 hm

theorem T_rec (n k : ℕ) :
    ((n : ℝ) + 3) * T (n + 2) (k + 1) =
      (2 * n + 3) * ((T (n + 1) (k + 1) : ℝ) + 2 * T (n + 1) k) - n * T n (k + 1) := by
  rw [T_eq, T_eq, T_eq, T_eq]
  have e1 : f (k + 1) ((n + 2 : ℕ) : ℤ) = ((n : ℤ) + k + 3) * (n + k + 2) * f k ((n + 1 : ℕ) : ℤ) := by
    rw [show ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 by push_cast; ring, f_shift]
    push_cast
    ring
  have e2 : f (k + 1) ((n + 1 : ℕ) : ℤ) = ((n : ℤ) + k + 2) * (n + 1 - k) * f k ((n + 1 : ℕ) : ℤ) := by
    rw [f_succ]
    push_cast
    ring
  have e3 : f (k + 1) (n : ℤ) = ((n : ℤ) + k + 1) * (n - k) * f k n := f_succ k n
  have e4 : f (k + 1) ((n + 1 : ℕ) : ℤ) = ((n : ℤ) + k + 2) * (n + k + 1) * f k n := by
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, f_shift]
  have R : ((n : ℤ) + 1 - k) * f k ((n + 1 : ℕ) : ℤ) = ((n : ℤ) + k + 1) * f k n := by
    have h := e2.symm.trans e4
    have hne : ((n : ℤ) + k + 2) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    linear_combination h
  have RR : ((n : ℝ) + 1 - k) * (f k ((n + 1 : ℕ) : ℤ) : ℝ) = ((n : ℝ) + k + 1) * (f k n : ℝ) := by
    exact_mod_cast R
  rw [e1, e2, e3, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  generalize f k ((n + 1 : ℕ) : ℤ) = A at RR ⊢
  generalize f k (n : ℤ) = B at RR ⊢
  push_cast
  have hp : ((n : ℝ) + k + 1) ≠ 0 := by positivity
  have hB : (B : ℝ) = ((n : ℝ) + 1 - k) * A / ((n : ℝ) + k + 1) := by
    field_simp
    linarith [RR]
  rw [hB]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem sum_ext (n m : ℕ) (g : ℕ → ℝ) (hm : n + 1 ≤ m) :
    ∑ k ∈ range m, g k * T n k = ∑ k ∈ range (n + 1), g k * T n k := by
  symm
  apply Finset.sum_subset (range_subset_range.mpr hm)
  intro k _ hk
  simp only [mem_range, not_lt] at hk
  rw [T_zero_of_lt n k (by omega)]
  simp

theorem r_eq (n m : ℕ) (hm : n + 1 ≤ m) : r n = ∑ k ∈ range m, (T n k : ℝ) := by
  have := sum_ext n m (fun _ => 1) hm
  simp only [one_mul] at this
  rw [this, r]

theorem U_eq (n m : ℕ) (hm : n + 1 ≤ m) : U n = ∑ k ∈ range m, (k : ℝ) * T n k := by
  rw [sum_ext n m (fun k => (k : ℝ)) hm, U]

theorem r_rec (n : ℕ) : ((n : ℝ) + 3) * r (n + 2) = 3 * (2 * n + 3) * r (n + 1) - n * r n := by
  have hr2 : r (n + 2) = ∑ k ∈ range (n + 2), (T (n + 2) (k + 1) : ℝ) + 1 := by
    rw [r_eq (n + 2) (n + 3) le_rfl, sum_range_succ', T_n_zero]
    simp
  have hr1 : r (n + 1) = ∑ k ∈ range (n + 2), (T (n + 1) (k + 1) : ℝ) + 1 := by
    rw [r_eq (n + 1) (n + 3) (by omega), sum_range_succ', T_n_zero]
    simp
  have hr1' : r (n + 1) = ∑ k ∈ range (n + 2), (T (n + 1) k : ℝ) := r_eq (n + 1) (n + 2) le_rfl
  have hr0 : r n = ∑ k ∈ range (n + 2), (T n (k + 1) : ℝ) + 1 := by
    rw [r_eq n (n + 3) (by omega), sum_range_succ', T_n_zero]
    simp
  have key : ∑ k ∈ range (n + 2), (((n : ℝ) + 3) * T (n + 2) (k + 1) -
      ((2 * n + 3) * ((T (n + 1) (k + 1) : ℝ) + 2 * T (n + 1) k) - n * T n (k + 1))) = 0 :=
    sum_eq_zero (fun k _ => by rw [T_rec n k]; ring)
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, sum_add_distrib,
    ← mul_sum] at key
  linear_combination key + ((n : ℝ) + 3) * hr2 + (n : ℝ) * hr0 - (2 * (n : ℝ) + 3) * hr1 -
    2 * (2 * (n : ℝ) + 3) * hr1'

theorem U_rec (n : ℕ) :
    ((n : ℝ) + 3) * U (n + 2) = (2 * n + 3) * (3 * U (n + 1) + 2 * r (n + 1)) - n * U n := by
  have hU2 : U (n + 2) = ∑ k ∈ range (n + 2), ((k : ℝ) + 1) * T (n + 2) (k + 1) := by
    rw [U_eq (n + 2) (n + 3) le_rfl, sum_range_succ']
    simp
  have hU1 : U (n + 1) = ∑ k ∈ range (n + 2), ((k : ℝ) + 1) * T (n + 1) (k + 1) := by
    rw [U_eq (n + 1) (n + 3) (by omega), sum_range_succ']
    simp
  have hU1' : U (n + 1) + r (n + 1) = ∑ k ∈ range (n + 2), ((k : ℝ) + 1) * T (n + 1) k := by
    rw [U_eq (n + 1) (n + 2) le_rfl, r_eq (n + 1) (n + 2) le_rfl, ← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  have hU0 : U n = ∑ k ∈ range (n + 2), ((k : ℝ) + 1) * T n (k + 1) := by
    rw [U_eq n (n + 3) (by omega), sum_range_succ']
    simp
  have key : ∑ k ∈ range (n + 2), (((n : ℝ) + 3) * (((k : ℝ) + 1) * T (n + 2) (k + 1)) -
      ((2 * n + 3) * (((k : ℝ) + 1) * T (n + 1) (k + 1) + 2 * (((k : ℝ) + 1) * T (n + 1) k)) -
        n * (((k : ℝ) + 1) * T n (k + 1)))) = 0 :=
    sum_eq_zero (fun k _ => by linear_combination ((k : ℝ) + 1) * T_rec n k)
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, sum_add_distrib,
    ← mul_sum] at key
  rw [hU2, hU0]
  linear_combination key - (2 * (n : ℝ) + 3) * hU1 - 2 * (2 * (n : ℝ) + 3) * hU1'

theorem r_small : r 0 = 1 ∧ r 1 = 2 ∧ r 2 = 6 := by
  have a : T 1 1 = 1 := by decide
  have b : T 2 1 = 3 := by decide
  have c : T 2 2 = 2 := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [r, sum_range_succ, T_n_zero, a, b, c] <;> norm_num

theorem U_small : U 1 = 1 ∧ U 2 = 7 := by
  have a : T 1 1 = 1 := by decide
  have b : T 2 1 = 3 := by decide
  have c : T 2 2 = 2 := by decide
  refine ⟨?_, ?_⟩ <;> norm_num [U, sum_range_succ, a, b, c]

/-- Exact formula: 4 U(n+1) = (3n+2) r(n+1) - n r(n). -/
theorem A088617_total (n : ℕ) : 4 * U (n + 1) = (3 * n + 2) * r (n + 1) - n * r n := by
  have pair : ∀ n : ℕ, (4 * U (n + 1) = (3 * n + 2) * r (n + 1) - n * r n) ∧
      (4 * U (n + 2) = (3 * ((n + 1 : ℕ) : ℝ) + 2) * r (n + 2) - ((n + 1 : ℕ) : ℝ) * r (n + 1)) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨h0, h1, h2⟩ := r_small
      obtain ⟨u1, u2⟩ := U_small
      refine ⟨?_, ?_⟩
      · simp [u1, h1]; norm_num
      · simp [u2, h1, h2]; norm_num
    | succ n ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have H1 := ih.1
      have H2 := ih.2
      have Rr3 := r_rec (n + 1)
      have RU3 := U_rec (n + 1)
      have Rr2 := r_rec n
      push_cast at H2 Rr3 RU3 ⊢
      have hne : ((n : ℝ) + 4) ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      linear_combination 4 * RU3 - (3 * (n : ℝ) + 8) * Rr3 + (6 * (n : ℝ) + 15) * H2 -
        ((n : ℝ) + 1) * H1 + ((n : ℝ) + 1) * Rr2
  exact (pair n).1

theorem r_pos (n : ℕ) : 0 < r n := by
  have h : (T n 0 : ℝ) ≤ r n :=
    single_le_sum (f := fun k => (T n k : ℝ)) (fun k _ => by positivity) (by simp)
  rw [T_n_zero] at h
  push_cast at h
  linarith

/-- x(n) = r(n+1)/r(n). -/
noncomputable def x (n : ℕ) : ℝ := r (n + 1) / r n

theorem x_rec (n : ℕ) : ((n : ℝ) + 3) * x (n + 1) = 3 * (2 * n + 3) - n / x n := by
  have h0 := r_pos n
  have h1 := r_pos (n + 1)
  have h2 : r (n + 1 + 1) = (3 * (2 * (n : ℝ) + 3) * r (n + 1) - n * r n) / ((n : ℝ) + 3) := by
    rw [eq_div_iff (by positivity)]
    linarith [r_rec n]
  unfold x
  rw [h2]
  field_simp

theorem x_bounds (n : ℕ) :
    2 ≤ x n ∧ x n ≤ 3 + 2 * Real.sqrt 2 ∧ ((n : ℝ) + 1) * (3 + 2 * Real.sqrt 2 - x n) ≤ 20 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : 1.4 < Real.sqrt 2 := by nlinarith
  have hs2 : Real.sqrt 2 < 1.5 := by nlinarith
  set s := Real.sqrt 2
  induction n with
  | zero =>
    have : x 0 = 2 := by
      obtain ⟨h0, h1, -⟩ := r_small
      simp [x, h0, h1]
    rw [this]
    refine ⟨le_rfl, by linarith, by push_cast; linarith⟩
  | succ n ih =>
    obtain ⟨hy2, hya, hye⟩ := ih
    have hrec := x_rec n
    set y := x n
    set y' := x (n + 1)
    set z := (n : ℝ) / y with hz
    have hyz : z * y = n := by rw [hz]; field_simp
    have hz0 : 0 ≤ z := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hzn : z * 2 ≤ n := by nlinarith
    have hzb : (n : ℝ) * (3 - 2 * s) ≤ z := by nlinarith
    have hn3 : (0 : ℝ) < n + 3 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · push_cast
      have hzr : z - n * (3 - 2 * s) = (3 - 2 * s) * z * (3 + 2 * s - y) := by
        linear_combination (3 - 2 * s) * hyz + 4 * z * hs
      have hze : z * (3 + 2 * s - y) ≤ 10 := by nlinarith
      have he : ((n : ℝ) + 3) * (3 + 2 * s - y') ≤ 20 := by nlinarith
      have hpos : 0 ≤ 3 + 2 * s - y' := by nlinarith
      nlinarith

theorem x_tendsto : Tendsto x atTop (𝓝 (3 + 2 * Real.sqrt 2)) := by
  have hb : Tendsto (fun n : ℕ => 20 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 20
  have he : Tendsto (fun n => 3 + 2 * Real.sqrt 2 - x n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by linarith [(x_bounds n).2.1]) _ hb
    intro n
    obtain ⟨-, -, h⟩ := x_bounds n
    have hp : (0 : ℝ) < n + 1 := by positivity
    rw [mul_one_div, le_div_iff₀ hp]
    linarith
  have := he.const_sub (3 + 2 * Real.sqrt 2)
  simpa using this

/-- Callan's conjecture (A088617): mean number of U steps / n -> sqrt(1/2). -/
theorem A088617_conjecture :
    Tendsto (fun n : ℕ => (∑ k ∈ range (n + 1), (k : ℝ) * T n k) /
      (∑ k ∈ range (n + 1), (T n k : ℝ)) / n) atTop (𝓝 (Real.sqrt (1 / 2))) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hα : (0 : ℝ) < 3 + 2 * Real.sqrt 2 := by positivity
  have hlim : Tendsto (fun n : ℕ => 3 / 4 - 1 / 4 * (1 / ((n : ℝ) + 1)) -
      1 / 4 * ((n : ℝ) / (n + 1)) * (x n)⁻¹) atTop
      (𝓝 (3 / 4 - 1 / 4 * 0 - 1 / 4 * 1 * (3 + 2 * Real.sqrt 2)⁻¹)) := by
    refine ((tendsto_const_nhds.sub ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul _)).sub
      (((tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul _).mul (x_tendsto.inv₀ hα.ne')))
  have hval : 3 / 4 - 1 / 4 * 0 - 1 / 4 * 1 * (3 + 2 * Real.sqrt 2)⁻¹ = Real.sqrt (1 / 2) := by
    rw [show (1 / 2 : ℝ) = (Real.sqrt 2 / 2) ^ 2 by rw [div_pow, hs]; norm_num,
      Real.sqrt_sq (by positivity)]
    field_simp
    linear_combination (-8 : ℝ) * hs
  rw [hval] at hlim
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hlim.congr (fun n => ?_)
  have hf := A088617_total n
  have h0 := r_pos n
  have h1 := r_pos (n + 1)
  change _ = U (n + 1) / r (n + 1) / ((n + 1 : ℕ) : ℝ)
  unfold x
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * hf

end A088617

open A088617
