import Mathlib
import PNTPlus.Consequences

/-
OEIS A119659, conjecture: (3,5,11), (5,11,17), (11,17,31) are the only triples of
consecutive prime-indexed primes q_n = p_{p_n} (A006450) that do not form a triangle.

What is checked here: the eventual form. `A119659.A119659_eventually`: for all
sufficiently large n, q(n+2) < q(n) + q(n+1). Route: P(k+1) ≤ 1.1 P(k) eventually
(`pn_pn_plus_one`) and 0.9 k log k ≤ P(k) ≤ 1.1 k log k eventually (`nth_prime_asymp`),
both from the vendored PrimeNumberTheoremAnd library (lib/PNTPlus); then
q(n+2) < 2 q(n) ≤ q(n) + q(n+1).

Not checked here: an explicit threshold for "sufficiently large" (the PNT used is
ineffective), hence not the full claim. The README's complete proof uses explicit bounds
(Nagura 1952, Rosser–Schoenfeld 1962, Rosser 1938) and a finite check (certificate/check.py);
those stay outside Lean. Indexing: q here is 0-indexed, q 0 = 3 = OEIS q_1.
-/

open Filter Topology Real Asymptotics

namespace A119659

/-- The k-th prime, 0-indexed (P 0 = 2). -/
noncomputable abbrev P (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- Prime-indexed primes A006450, 0-indexed: q 0 = 3, q 1 = 5, q 2 = 11, ...
(OEIS q_n = p_{p_n} with p_1 = 2 is q (n - 1)). -/
noncomputable def q (n : ℕ) : ℕ := P (P n - 1)

theorem P_mono : Monotone P := Nat.nth_monotone Nat.infinite_setOfPred_prime

theorem q_mono : Monotone q := fun _ _ h => P_mono (Nat.sub_le_sub_right (P_mono h) 1)

/-- Eventually P (k + 1) ≤ 11/10 · P k (consecutive primes have ratio → 1). -/
theorem P_succ_le : ∀ᶠ k : ℕ in atTop, (P (k + 1) : ℝ) ≤ 11 / 10 * P k := by
  obtain ⟨c, hc, hP⟩ := pn_pn_plus_one
  have hc0 := (isLittleO_one_iff ℝ).mp hc
  filter_upwards [(tendsto_order.1 hc0).2 (1 / 10) (by norm_num)] with k hk
  have h := hP k
  have hpos : (0 : ℝ) ≤ P k := Nat.cast_nonneg _
  have hle : P k ≤ P (k + 1) := P_mono (Nat.le_succ k)
  simp only [nth_prime] at h
  nlinarith

/-- Eventually 9/10 · k log k ≤ P k ≤ 11/10 · k log k. -/
theorem P_bounds : ∀ᶠ k : ℕ in atTop,
    9 / 10 * ((k : ℝ) * log k) ≤ P k ∧ (P k : ℝ) ≤ 11 / 10 * ((k : ℝ) * log k) := by
  have hpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (k : ℝ) * log k := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    have : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
    exact mul_pos (by linarith) (log_pos this)
  have h := (isEquivalent_iff_tendsto_one (hpos.mono fun k hk => hk.ne')).mp nth_prime_asymp
  filter_upwards [(tendsto_order.1 h).1 (9 / 10) (by norm_num),
    (tendsto_order.1 h).2 (11 / 10) (by norm_num), hpos] with k h1 h2 h3
  simp only [Pi.div_apply, nth_prime] at h1 h2
  rw [lt_div_iff₀ h3] at h1
  rw [div_lt_iff₀ h3] at h2
  exact ⟨h1.le, h2.le⟩

theorem log_five_fourths_lt : log (5 / 4 : ℝ) < 1 / 4 := by
  have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4) (by norm_num)
  linarith

/-- Eventually, P M < 2 P m whenever M ≤ 5/4 · m. -/
theorem P_ratio : ∀ᶠ m : ℕ in atTop, ∀ M : ℕ, (M : ℝ) ≤ 5 / 4 * m → (P M : ℝ) < 2 * P m := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp P_bounds
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 3] with m hmK hm3 M hM
  set M' := max M m with hM'
  have hM'K : K ≤ M' := le_trans hmK (le_max_right _ _)
  have hM'le : (M' : ℝ) ≤ 5 / 4 * m := by
    rw [hM']; push_cast
    have : (m : ℝ) ≤ 5 / 4 * m := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    exact max_le hM this
  have hm0 : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hM'1 : (1 : ℝ) ≤ M' := by
    have : (m : ℝ) ≤ M' := by exact_mod_cast le_max_right M m
    linarith
  have hPM : (P M : ℝ) ≤ P M' := by exact_mod_cast P_mono (le_max_left M m)
  have hup := (hK M' hM'K).2
  have hlo := (hK m hmK).1
  have hlogm : 1 < log (m : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogM' : log (M' : ℝ) ≤ log (5 / 4 : ℝ) + log m := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact log_le_log (by linarith) hM'le
  have hl54 := log_five_fourths_lt
  have hlogM'0 : 0 ≤ log (M' : ℝ) := log_nonneg hM'1
  have hkey : (M' : ℝ) * log M' ≤ 5 / 4 * m * (1 / 4 + log m) := by
    apply mul_le_mul hM'le (by linarith) hlogM'0 (by positivity)
  nlinarith

/-- **A119659, eventual form**: for all large n, q n + q (n + 1) > q (n + 2), so
consecutive prime-indexed primes form a triangle. -/
theorem A119659_eventually : ∀ᶠ n : ℕ in atTop, q (n + 2) < q n + q (n + 1) := by
  have hm : Tendsto (fun n : ℕ => P n - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp tendsto_nth_prime_atTop
  have hratio := hm.eventually P_ratio
  have hstep := P_succ_le
  filter_upwards [hratio, hstep, (tendsto_add_atTop_nat 1).eventually hstep,
    hm.eventually (eventually_ge_atTop 10)] with n h1 h2 h3 h4
  have hPn : 1 ≤ P n := (Nat.prime_nth_prime n).one_lt.le
  have hP2 : 1 ≤ P (n + 2) := (Nat.prime_nth_prime (n + 2)).one_lt.le
  have hbound : (P (n + 2) : ℝ) ≤ 121 / 100 * P n := by
    have h3' : (P (n + 1 + 1) : ℝ) ≤ 11 / 10 * P (n + 1) := h3
    have : (0 : ℝ) ≤ P n := Nat.cast_nonneg _
    nlinarith
  have hM : ((P (n + 2) - 1 : ℕ) : ℝ) ≤ 5 / 4 * ((P n - 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hPn, Nat.cast_sub hP2]
    have : (10 : ℝ) ≤ ((P n - 1 : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast [Nat.cast_sub hPn] at this
    nlinarith
  have hlt := h1 _ hM
  have hq : q n ≤ q (n + 1) := q_mono (Nat.le_succ n)
  have : (q (n + 2) : ℝ) < 2 * q n := hlt
  have : (q n : ℝ) ≤ q (n + 1) := by exact_mod_cast hq
  have : (q (n + 2) : ℝ) < q n + q (n + 1) := by linarith
  exact_mod_cast this
