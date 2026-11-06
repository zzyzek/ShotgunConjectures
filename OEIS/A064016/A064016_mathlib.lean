/-
OEIS A064016: a(n) = Sum_{k <= 10^n} cototient(k), cototient(k) = k - phi(k) (A051953).
Comment (entry): "It appears that lim_{n->infinity} (1/n^2) * Sum_{j=1..n} a(j)
= 0.1960364... = (1/2 - 3/Pi^2)."

Main theorems.
* `sum_totient_tendsto` (Mertens 1874): (Sum_{k=1..N} phi(k)) / N^2 -> 3/pi^2.
* `sum_cototient_tendsto`: (Sum_{k=1..N} cototient(k)) / N^2 -> 1/2 - 3/pi^2.
* `A064016_tendsto` (the intended statement): a(n) / 10^(2n) -> 1/2 - 3/pi^2.
* `A064016_literal_false`: (1/n^2) Sum_{j=1..n} a(j) -> +infinity, so the comment
  as printed is false.

Route. phi = mu * id (Moebius inversion of Sum_{d|n} phi(d) = n), so
Sum_{n<=N} phi(n) = Sum_{d<=N} mu(d) T(N/d), T(M) = M(M+1)/2
(`ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`); Tannery's theorem with bound
1/d^2 gives the limit (1/2) Sum mu(d)/d^2, and Sum mu(d)/d^2 = 1/zeta(2) = 6/pi^2
(`LSeries_zeta_mul_Lseries_moebius`, `riemannZeta_two`).

Not checked in this file: agreement with the OEIS data (certificate/check.py).
-/
import Mathlib

open ArithmeticFunction Finset Filter Topology Real
open scoped ArithmeticFunction.Moebius

namespace A064016

/-- The cototient A051953. -/
def cototient (k : ℕ) : ℕ := k - k.totient

/-- OEIS A064016. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Icc 1 (10 ^ n), cototient k

lemma totient_eq_moebius (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * (x.2 : ℝ) = (n.totient : ℝ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (f := fun n => (n.totient : ℝ))
    (g := fun n => (n : ℝ))).1 (fun n _ => by exact_mod_cast Nat.sum_totient n)
  exact h n hn

lemma sum_id_Ioc (M : ℕ) : ∑ m ∈ Ioc 0 M, (m : ℝ) = M * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih]
    push_cast; ring

/-- T(M) = M(M+1)/2. -/
noncomputable def T (M : ℕ) : ℝ := M * (M + 1) / 2

lemma sum_totient_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n.totient : ℝ) = ∑ d ∈ Ioc 0 N, (μ d : ℝ) * T (N / d) := by
  have h1 : ∀ n ∈ Ioc 0 N, (n.totient : ℝ) =
      ((↑μ : ArithmeticFunction ℝ) * (↑(ArithmeticFunction.id) : ArithmeticFunction ℝ)) n := by
    intro n hn
    rw [mul_apply, ← totient_eq_moebius n (Finset.mem_Ioc.1 hn).1]
    apply Finset.sum_congr rfl
    intro x _
    simp [intCoe_apply, natCoe_apply, id_apply]
  rw [Finset.sum_congr rfl h1, sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [T, ← sum_id_Ioc]
  simp [intCoe_apply, natCoe_apply, id_apply]

theorem tsum_moebius_sq : ∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 = 6 / π ^ 2 := by
  have h := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_zeta_eq_riemannZeta (by norm_num), riemannZeta_two] at h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hL : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 = 6 / (π : ℂ) ^ 2 := by
    field_simp
    linear_combination 6 * h
  have hR : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 =
      ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1
    funext n
    rw [LSeries.term_def]
    split_ifs with h0
    · simp [h0]
    · push_cast
      congr 1
      norm_cast
  have := hR.symm.trans hL
  exact_mod_cast this

/-- The d-th term of the Moebius expression for (Sum_{n<=N} phi(n)) / N^2. -/
noncomputable def F (N d : ℕ) : ℝ := (μ d : ℝ) * T (N / d) / (N : ℝ) ^ 2

/-- Its limit as N -> infinity. -/
noncomputable def G (d : ℕ) : ℝ := (μ d : ℝ) / (d : ℝ) ^ 2 / 2

lemma F_tsum (N : ℕ) : ∑' d, F N d = (∑ n ∈ Ioc 0 N, (n.totient : ℝ)) / (N : ℝ) ^ 2 := by
  rw [sum_totient_eq, Finset.sum_div, tsum_eq_sum (s := Ioc 0 N)]
  · rfl
  · intro d hd
    simp only [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hd
    rcases hd with hd | hd
    · have : d = 0 := by omega
      subst this; simp [F]
    · have : N / d = 0 := Nat.div_eq_of_lt hd
      simp [F, this, T]

lemma T_le (q : ℕ) : T q ≤ (q : ℝ) ^ 2 := by
  unfold T
  have : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h
      nlinarith
  nlinarith

lemma T_nonneg (q : ℕ) : 0 ≤ T q := by unfold T; positivity

lemma F_bound (N d : ℕ) : ‖F N d‖ ≤ 1 / (d : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [F]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [F]
  have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : ((N / d : ℕ) : ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  have hq0 : (0 : ℝ) ≤ ((N / d : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, F, abs_div, abs_mul, abs_of_nonneg (T_nonneg _),
    abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |(μ d : ℝ)| * T (N / d) ≤ ((N / d : ℕ) : ℝ) ^ 2 :=
    le_trans (mul_le_of_le_one_left (T_nonneg _) hmu) (T_le _)
  have h2 : ((N / d : ℕ) : ℝ) ^ 2 * (d : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hq 2
  nlinarith

lemma ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 (1 / d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlow : Tendsto (fun N : ℕ => 1 / (d : ℝ) - 1 / N) atTop (𝓝 (1 / d)) := by
    have h1N : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := 1 / (d : ℝ))).sub h1N
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hlt : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by
      exact_mod_cast Nat.lt_div_mul_add hd
    rw [div_sub_div _ _ hdR.ne' hNR.ne', div_le_div_iff₀ (by positivity) hNR]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hq : ((N / d : ℕ) : ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
    rw [div_le_div_iff₀ hNR hdR]
    linarith

lemma F_tendsto (d : ℕ) : Tendsto (fun N => F N d) atTop (𝓝 (G d)) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [F, G]
  have hr := ratio_tendsto d hd
  have h1N : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Tendsto (fun N : ℕ => (μ d : ℝ) *
      ((((N / d : ℕ) : ℝ) / N) * ((((N / d : ℕ) : ℝ) / N) + 1 / N)) / 2) atTop
      (𝓝 ((μ d : ℝ) * ((1 / d) * (1 / d + 0)) / 2)) :=
    ((tendsto_const_nhds.mul (hr.mul (hr.add h1N))).div_const 2)
  have hG : (μ d : ℝ) * ((1 / d) * (1 / d + 0)) / 2 = G d := by
    unfold G; field_simp; ring
  rw [hG] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold F T
  field_simp

theorem sum_totient_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (n.totient : ℝ)) / (N : ℝ) ^ 2) atTop
      (𝓝 (3 / π ^ 2)) := by
  have h := tendsto_tsum_of_dominated_convergence (f := F) (g := G)
    (bound := fun d : ℕ => 1 / (d : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.2 one_lt_two) F_tendsto
    (Eventually.of_forall (fun N d => F_bound N d))
  have hG : ∑' d, G d = 3 / π ^ 2 := by
    unfold G
    rw [tsum_div_const, tsum_moebius_sq]
    ring
  rw [hG] at h
  refine h.congr (fun N => ?_)
  have hI : Icc 1 N = Ioc 0 N := by ext; simp; omega
  rw [F_tsum, hI]

theorem sum_cototient_tendsto :
    Tendsto (fun N : ℕ => (∑ k ∈ Icc 1 N, (cototient k : ℝ)) / (N : ℝ) ^ 2) atTop
      (𝓝 (1 / 2 - 3 / π ^ 2)) := by
  have h1N : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hhalf : Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) / 2) atTop (𝓝 (1 / 2)) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add h1N).div_const (2 : ℝ)
    simpa using this
  refine (hhalf.sub sum_totient_tendsto).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hI : Icc 1 N = Ioc 0 N := by ext; simp; omega
  have hc : ∀ k ∈ Icc 1 N, (cototient k : ℝ) = (k : ℝ) - (k.totient : ℝ) := by
    intro k _; unfold cototient; rw [Nat.cast_sub (Nat.totient_le k)]
  rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, hI, sum_id_Ioc]
  field_simp

/-- The intended statement: a(n) / 10^(2n) -> 1/2 - 3/pi^2. -/
theorem A064016_tendsto :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((10 : ℝ) ^ n) ^ 2) atTop (𝓝 (1 / 2 - 3 / π ^ 2)) := by
  have h10 : Tendsto (fun n : ℕ => 10 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 10)
  refine (sum_cototient_tendsto.comp h10).congr (fun n => ?_)
  simp only [Function.comp, a]
  push_cast
  rfl

lemma const_pos : 0 < 1 / 2 - 3 / π ^ 2 := by
  have h := Real.pi_gt_three
  have : 9 < π ^ 2 := by nlinarith
  have : 3 / π ^ 2 < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- The comment as printed is false: (1/n^2) Sum_{j=1..n} a(j) -> +infinity. -/
theorem A064016_literal_false :
    Tendsto (fun n : ℕ => (∑ j ∈ Icc 1 n, (a j : ℝ)) / (n : ℝ) ^ 2) atTop atTop := by
  set c := 1 / 2 - 3 / π ^ 2 with hc
  have hc0 : 0 < c := const_pos
  have hev : ∀ᶠ n : ℕ in atTop, c / 2 < (a n : ℝ) / ((10 : ℝ) ^ n) ^ 2 :=
    A064016_tendsto.eventually (lt_mem_nhds (by linarith))
  have hlin : Tendsto (fun n : ℕ => c / 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : (0 : ℝ) < ((10 : ℝ) ^ n) ^ 2 := by positivity
  have h1 : c / 2 * ((10 : ℝ) ^ n) ^ 2 ≤ a n := by
    rw [lt_div_iff₀ hpow] at hn; exact hn.le
  have h2 : (n : ℝ) ^ 3 ≤ ((10 : ℝ) ^ n) ^ 2 := by
    have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have : (n : ℝ) ^ 3 ≤ ((2 : ℝ) ^ n) ^ 3 := pow_le_pow_left₀ (by positivity) h2n.le 3
    calc (n : ℝ) ^ 3 ≤ ((2 : ℝ) ^ n) ^ 3 := this
      _ = (8 : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (100 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      _ = ((10 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h3 : (a n : ℝ) ≤ ∑ j ∈ Icc 1 n, (a j : ℝ) :=
    Finset.single_le_sum (f := fun j => (a j : ℝ)) (fun j _ => Nat.cast_nonneg _)
      (Finset.mem_Icc.2 ⟨hn1, le_rfl⟩)
  rw [le_div_iff₀ (by positivity)]
  have : c / 2 * (n : ℝ) * (n : ℝ) ^ 2 = c / 2 * (n : ℝ) ^ 3 := by ring
  rw [this]
  nlinarith
