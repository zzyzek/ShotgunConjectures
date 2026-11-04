/-
OEIS A102613, conjecture: π(n)/(n − π(n)) tends to 0 as n → ∞.

Main theorem `A102613_conjecture`: the real sequence π(n)/(n − π(n)), with
π = `Nat.primeCounting`, tends to 0 along ℕ.  This is the README result.
Proof: Chebyshev's upper bound in Mathlib (`Chebyshev.eventually_primeCounting_le`)
gives π(n) ≤ (log 4 + 1)·n/log n eventually, so π(n)/n → 0, and
π(n)/(n − π(n)) = (π(n)/n)/(1 − π(n)/n).

Not checked: nothing outside Lean.
-/
import Mathlib

open Filter Topology Real

theorem primeCounting_div_tendsto_zero :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / n) atTop (𝓝 0) := by
  have hC := (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have hC' := tendsto_natCast_atTop_atTop.eventually hC
  have hlog : Tendsto (fun n : ℕ => (log 4 + 1) / log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [hC', eventually_ge_atTop 2] with n hn h2
    simp only [Nat.floor_natCast] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [div_le_iff₀ hn0]
    calc (Nat.primeCounting n : ℝ) ≤ (log 4 + 1) * n / log n := hn
      _ = (log 4 + 1) / log n * n := by ring

theorem A102613_conjecture :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) - Nat.primeCounting n))
      atTop (𝓝 0) := by
  have h := primeCounting_div_tendsto_zero
  have h2 : Tendsto (fun n : ℕ => ((Nat.primeCounting n : ℝ) / n) /
      (1 - (Nat.primeCounting n : ℝ) / n)) atTop (𝓝 (0 / (1 - 0))) :=
    h.div (tendsto_const_nhds.sub h) (by norm_num)
  rw [zero_div] at h2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [one_sub_div hn0, div_div_div_cancel_right₀ hn0]
