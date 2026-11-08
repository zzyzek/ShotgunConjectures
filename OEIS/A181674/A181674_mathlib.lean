import Mathlib
import OpenProblemsLib.PNTApps

/-
OEIS A181674.  a(n) = number of ways to write n = P + m with P a primorial (A002110, 1 included)
and m a semiprime.  Conjecture (C. R. Greathouse IV, 2011): the average order is
Theta(log log n).  Refuted: the mean (1/x) sum_{n ≤ x} a(n) is bounded.

Checked here.
* `A181674_sum_le_mul`: sum_{n ≤ x} a(n) ≤ K(x) S(x), K = number of primorials ≤ x,
  S = number of semiprimes ≤ x.
* `primorial_count_le`: K(x) ≤ M for some M with M! ≤ x (the k-th primorial is at least
  (k+1)!, `factorial_le_primorial`).
* `A181674_sum_le`: there is C with sum_{n ≤ x} a(n) ≤ C x for all x ≥ 16.  Inputs: the
  semiprime bound `semiprime_count_bound` of OpenProblemsLib.PNTApps (Chebyshev's bound from
  Mathlib plus a dyadic Mertens bound), `key_ineq` (M (1 + log J) ≤ 29 J when M! ≤ 2^J).
* `A181674_not_loglog`: there is no c > 0 with c log log x ≤ (1/x) sum_{n ≤ x} a(n) for all
  large x; so the average order is not Theta(log log n).
Not checked here: the sharper statement that the mean tends to 1 (README, lower bound via the
prime number theorem).  Axioms propext, Classical.choice, Quot.sound.
-/

namespace A181674

open Real Finset OpenProblemsLib.PNTApps


theorem primeCounting_le_pred (n : ℕ) : Nat.primeCounting n ≤ n - 1 := by
  rcases n with _ | n
  · simp
  · rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ', Nat.count_succ']
    simp only [zero_add, Nat.not_prime_zero, Nat.not_prime_one, ↓reduceIte, add_zero]
    exact le_of_le_of_eq (Nat.count_le _) (by omega)

theorem primorial_succ' (n : ℕ) :
    primorial (n + 1) = primorial n * (if (n + 1).Prime then n + 1 else 1) := by
  simp only [primorial, Finset.range_add_one (n := n + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.prod_insert (by simp), mul_comm]
  · rw [mul_one]

theorem factorial_le_primorial (n : ℕ) : (Nat.primeCounting n + 1).factorial ≤ primorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [primorial_succ']
    have hpc : Nat.primeCounting (n + 1) =
        Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
      simp only [Nat.primeCounting, Nat.primeCounting']
      rw [Nat.count_succ]
    split_ifs at hpc ⊢ with h
    · rw [hpc, Nat.factorial_succ, mul_comm]
      have h1 := primeCounting_le_pred n
      have h2 : 1 ≤ n := by have := h.two_le; omega
      exact Nat.mul_le_mul ih (by omega)
    · rw [hpc, add_zero, mul_one]; exact ih

/-- `P` is a primorial (A002110, `1` included). -/
def IsPrimorial (P : ℕ) : Prop := ∃ n, primorial n = P

theorem primesLE_eq_of_card {n n' : ℕ} (h : Nat.primeCounting n = Nat.primeCounting n') :
    (range (n + 1)).filter Nat.Prime = (range (n' + 1)).filter Nat.Prime := by
  rw [primeCounting_eq_card, primeCounting_eq_card] at h
  rcases le_total n n' with hle | hle
  · exact Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr (by omega))) h.ge
  · exact (Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr (by omega))) h.le).symm

open Classical in
/-- The number of primorials up to `x` is at most some `M` with `M! ≤ x` (`x ≥ 1`). -/
theorem primorial_count_le (x : ℕ) (hx : 1 ≤ x) :
    ∃ M : ℕ, ((range (x + 1)).filter IsPrimorial).card ≤ M ∧ M.factorial ≤ x := by
  set T := (range (x + 1)).filter (fun k => (k + 1).factorial ≤ x)
  have hK : ((range (x + 1)).filter IsPrimorial).card ≤ T.card := by
    refine card_le_card_of_injOn (fun P => if h : IsPrimorial P then
      Nat.primeCounting (Nat.find h) else 0) ?_ ?_
    · intro P hP
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hP
      simp only [hP.2, dite_true, T, coe_filter, mem_range, Set.mem_ofPred_eq]
      have hspec := Nat.find_spec hP.2
      have hf := factorial_le_primorial (Nat.find hP.2)
      rw [hspec] at hf
      refine ⟨?_, by omega⟩
      have := Nat.self_le_factorial (Nat.primeCounting (Nat.find hP.2) + 1)
      omega
    · intro P hP P' hP' hEq
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hP hP'
      simp only [hP.2, hP'.2, dite_true] at hEq
      have e := primesLE_eq_of_card hEq
      rw [← Nat.find_spec hP.2, ← Nat.find_spec hP'.2]
      unfold primorial
      exact Finset.prod_congr e (fun _ _ => rfl)
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨0, by rw [hT] at hK; simpa using hK, by simpa using hx⟩
  · set k := T.max' hT
    have hkT := T.max'_mem hT
    simp only [T, mem_filter, mem_range] at hkT
    refine ⟨k + 1, hK.trans ?_, hkT.2⟩
    have : T ⊆ range (k + 1) := fun j hj => by
      rw [mem_range]; exact Nat.lt_succ_of_le (T.le_max' j hj)
    simpa using card_le_card this

/-! ## The real inequality `M (1 + log J) ≤ 29 J` when `M! ≤ 2^J` -/

theorem key_ineq (M J : ℕ) (hJ : 1 ≤ J) (hM : M.factorial ≤ 2 ^ J) :
    (M : ℝ) * (1 + log J) ≤ 29 * J := by
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hlogJ : 0 ≤ log (J : ℝ) := log_nonneg hJR
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · simp only [Nat.cast_zero, zero_mul]; linarith
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  -- `M (log M - 1) ≤ J`.
  have hst : (M : ℝ) * (log M - 1) ≤ J := by
    have h1 := Real.pow_div_factorial_le_exp (x := (M : ℝ)) (by positivity) M
    have hf : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
    rw [div_le_iff₀ hf] at h1
    have h2 : ((M.factorial : ℕ) : ℝ) ≤ (2 : ℝ) ^ J := by exact_mod_cast hM
    have h3 : (M : ℝ) ^ M ≤ exp M * 2 ^ J := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have h4 := log_le_log (by positivity) h3
    rw [log_mul (by positivity) (by positivity), log_exp, log_pow, log_pow] at h4
    have h5 : log (2 : ℝ) ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h6 : (J : ℝ) * log 2 ≤ J := by nlinarith
    nlinarith
  rcases le_or_gt ((M : ℝ) ^ 2) J with hsq | hsq
  · -- `M ≤ √J`, `log J ≤ 2 √J`.
    have hlj : log (J : ℝ) ≤ 2 * √(J : ℝ) := by
      have := log_le_rpow_div (x := (J : ℝ)) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← sqrt_eq_rpow] at this; linarith
    have hMs : (M : ℝ) ≤ √(J : ℝ) := by
      rw [show (M : ℝ) = √((M : ℝ) ^ 2) by rw [sqrt_sq (by positivity)]]
      exact sqrt_le_sqrt hsq
    have hsJ : √(J : ℝ) ≤ J := by
      rw [sqrt_le_left (by positivity)]; nlinarith
    have hss : √(J : ℝ) * √(J : ℝ) = J := mul_self_sqrt (by positivity)
    have : (M : ℝ) * (1 + log J) ≤ √(J : ℝ) * (1 + 2 * √(J : ℝ)) :=
      mul_le_mul hMs (by linarith) (by positivity) (sqrt_nonneg _)
    nlinarith
  · -- `log J < 2 log M` and `M ≤ J + 8`.
    have hlj : log (J : ℝ) ≤ 2 * log M := by
      have := log_le_log (by positivity) hsq.le
      rw [log_pow] at this; push_cast at this; linarith
    have hM8 : (M : ℝ) ≤ J + 8 := by
      rcases le_or_gt (M : ℝ) 8 with h | h
      · linarith
      · have he : (2 : ℝ) ≤ log M := by
          rw [le_log_iff_exp_le (by positivity)]
          have : exp (2 : ℝ) = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
          rw [this]
          have := exp_one_lt_d9
          nlinarith [exp_pos 1]
        nlinarith
    nlinarith


open Classical in
/-- `a(n)`: the primorials `P ≤ n` with `n - P` a semiprime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun P => IsPrimorial P ∧ IsSemiprime (n - P))).card

end A181674

open A181674 Real Finset OpenProblemsLib.PNTApps Filter Topology

open Classical in
theorem A181674_sum_le_mul (x : ℕ) : ∑ n ∈ range (x + 1), a n ≤
    ((range (x + 1)).filter IsPrimorial).card * ((range (x + 1)).filter IsSemiprime).card := by
  have h1 : ∀ n ∈ range (x + 1), a n = ∑ P ∈ range (x + 1),
      (if P ≤ n ∧ (IsPrimorial P ∧ IsSemiprime (n - P)) then 1 else 0) := by
    intro n hn
    rw [mem_range] at hn
    unfold a
    rw [card_filter, show range (n + 1) = (range (x + 1)).filter (· ≤ n) by
      ext P; simp only [mem_range, mem_filter]; omega, sum_filter]
    refine sum_congr rfl fun P _ => ?_
    simp only [ite_and]
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ P ∈ range (x + 1), (∑ n ∈ range (x + 1),
      (if P ≤ n ∧ (IsPrimorial P ∧ IsSemiprime (n - P)) then 1 else 0)) ≤
      if IsPrimorial P then ((range (x + 1)).filter IsSemiprime).card else 0 := by
    intro P _
    by_cases hP : IsPrimorial P
    · simp only [hP, true_and, ↓reduceIte]
      rw [← card_filter]
      refine card_le_card_of_injOn (fun n => n - P) ?_ ?_
      · intro n hn
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn ⊢
        exact ⟨by omega, hn.2.2⟩
      · intro n hn n' hn' h
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn hn'
        simp only at h
        omega
    · simp [hP]
  refine (sum_le_sum h2).trans (le_of_eq ?_)
  rw [← sum_filter, sum_const, smul_eq_mul]

theorem A181674_sum_le : ∃ C : ℝ, ∀ x : ℕ, 16 ≤ x →
    (∑ n ∈ range (x + 1), a n : ℝ) ≤ C * x := by
  classical
  obtain ⟨C, hC0, hC⟩ := semiprime_count_bound
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨58 * C / log 2, fun x hx => ?_⟩
  obtain ⟨M, hKM, hM⟩ := primorial_count_le x (by omega)
  set J := Nat.log 2 x + 1
  have hJ5 : 5 ≤ J := by
    have : 4 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
    omega
  have hx2 : x < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) x
  have hx1 : 2 ^ (J - 1) ≤ x := by
    have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    simpa [J] using this
  have hkey := key_ineq M J (by omega) (hM.trans hx2.le)
  have hxR : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx : ((J : ℝ) - 1) * log 2 ≤ log x := by
    have h := log_le_log (by positivity) (show ((2 ^ (J - 1) : ℕ) : ℝ) ≤ x by exact_mod_cast hx1)
    push_cast at h
    rw [log_pow] at h
    have : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this] at h; exact h
  have hJR : (5 : ℝ) ≤ J := by exact_mod_cast hJ5
  have hlogx' : (J : ℝ) * log 2 / 2 ≤ log x := by nlinarith
  have hlogpos : 0 < log (x : ℝ) := log_pos (by linarith)
  have hS := hC x hx
  have hK : (((range (x + 1)).filter IsPrimorial).card : ℝ) ≤ M := by exact_mod_cast hKM
  have hsum : (∑ n ∈ range (x + 1), a n : ℝ) ≤
      (((range (x + 1)).filter IsPrimorial).card : ℝ) *
        (((range (x + 1)).filter IsSemiprime).card : ℝ) := by
    exact_mod_cast A181674_sum_le_mul x
  have hlogJ : 0 ≤ 1 + log (J : ℝ) := by
    have := log_nonneg (show (1 : ℝ) ≤ J by linarith); linarith
  calc (∑ n ∈ range (x + 1), a n : ℝ)
      ≤ (((range (x + 1)).filter IsPrimorial).card : ℝ) *
          (((range (x + 1)).filter IsSemiprime).card : ℝ) := hsum
    _ ≤ M * (C * x * (1 + log J) / log x) :=
        mul_le_mul hK hS (by positivity) (by positivity)
    _ = C * x * (M * (1 + log J)) / log x := by ring
    _ ≤ C * x * (29 * J) / log x := by
        apply div_le_div_of_nonneg_right _ hlogpos.le
        exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ C * x * (29 * J) / ((J : ℝ) * log 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlogx'
    _ = 58 * C / log 2 * x := by field_simp; ring

/-- The average order of A181674 is not `Θ(log log n)`: no `c > 0` has
`c log log x ≤ (1/x) ∑_{n ≤ x} a(n)` for all large `x`. -/
theorem A181674_not_loglog : ¬ ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℕ in atTop, c * log (log x) ≤ (∑ n ∈ range (x + 1), a n : ℝ) / x := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨C, hC⟩ := A181674_sum_le
  have htend : Tendsto (fun x : ℕ => log (log (x : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hbig := htend.eventually_gt_atTop (C / c)
  obtain ⟨x, hx1, hx2, hx3⟩ := (hev.and (hbig.and (eventually_ge_atTop 16))).exists
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have h1 : (∑ n ∈ range (x + 1), a n : ℝ) / x ≤ C := by
    rw [div_le_iff₀ hxR]; exact hC x hx3
  have h2 : C < c * log (log x) := by
    rw [div_lt_iff₀ hc] at hx2; linarith
  linarith
