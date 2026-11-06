/-
OEIS A226187 (offset 1): a(n) = least positive integer k such that
1 + 1/2 + ... + 1/k > n/3.  Conjecture (entry text): a(n+1)/a(n) converges
to 1.39... (probably exp(1/3)).

Definition.  `A226187 n = Nat.find (exists_harmonic_gt n)`, the least k with
n/3 < H_k, where H_k = `harmonic k` (a rational, H_0 = 0).  Since H_0 = 0
and n/3 ≥ 0, the least such k is positive, so "least positive integer" and
"least natural number" agree.  The definition also covers n = 0 (a(0) = 1),
which does not affect the limit.

Main theorem.
* `A226187_ratio`: Tendsto (fun n => a(n+1) / a(n)) atTop (𝓝 (exp (1/3))).

Proof.  By minimality H_{a-1} ≤ n/3 < H_a with a = a(n), so
0 < H_a - n/3 ≤ 1/a.  a(n) → ∞ (H is monotone, so a(n) < N forces
n < 3 H_N).  With H_k - log k → γ (Mathlib `Real.tendsto_harmonic_sub_log`),
log a(n) - n/3 = (H_a - n/3) - (H_a - log a) → -γ.  Hence
log a(n+1) - log a(n) → 1/3 and the ratio tends to exp(1/3).

Not checked in this file: that `A226187 n` reproduces the OEIS data terms
(certificate/check.py compares numerically); no rate of convergence.
-/
import Mathlib

open Filter Topology

/-- The harmonic numbers are monotone. -/
theorem harmonic_monotone : Monotone harmonic := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [harmonic_succ]
  have : (0 : ℚ) ≤ (↑(n + 1))⁻¹ := by positivity
  linarith

/-- Some harmonic number exceeds n/3 (H_k ≥ log(k+1) is unbounded). -/
theorem exists_harmonic_gt (n : ℕ) : ∃ k, ((n : ℚ) / 3) < harmonic k := by
  refine ⟨⌈Real.exp ((n : ℝ) / 3)⌉₊, ?_⟩
  have h1 : Real.exp ((n : ℝ) / 3) ≤ (⌈Real.exp ((n : ℝ) / 3)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (n : ℝ) / 3 < Real.log ((⌈Real.exp ((n : ℝ) / 3)⌉₊ : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have h3 := log_add_one_le_harmonic ⌈Real.exp ((n : ℝ) / 3)⌉₊
  push_cast at h3
  have h4 : ((((n : ℚ) / 3 : ℚ)) : ℝ) < ((harmonic ⌈Real.exp ((n : ℝ) / 3)⌉₊ : ℚ) : ℝ) := by
    push_cast
    linarith
  exact Rat.cast_lt.mp h4

/-- a(n) = least k with H_k > n/3. -/
def A226187 (n : ℕ) : ℕ := Nat.find (exists_harmonic_gt n)

theorem a_spec (n : ℕ) : ((n : ℚ) / 3) < harmonic (A226187 n) :=
  Nat.find_spec (exists_harmonic_gt n)

theorem a_pos (n : ℕ) : 1 ≤ A226187 n := by
  by_contra h
  have h0 : A226187 n = 0 := by omega
  have hs := a_spec n
  rw [h0, harmonic_zero] at hs
  have : (0 : ℚ) ≤ (n : ℚ) / 3 := by positivity
  linarith

theorem a_prev (n : ℕ) : harmonic (A226187 n - 1) ≤ (n : ℚ) / 3 := by
  have h1 := a_pos n
  exact le_of_not_gt (Nat.find_min (exists_harmonic_gt n) (show A226187 n - 1 < A226187 n by omega))

theorem a_upper (n : ℕ) :
    (harmonic (A226187 n) : ℝ) ≤ (n : ℝ) / 3 + ((A226187 n : ℕ) : ℝ)⁻¹ := by
  have h1 := a_pos n
  have h2 := a_prev n
  obtain ⟨j, hj⟩ : ∃ j, A226187 n = j + 1 := ⟨A226187 n - 1, by omega⟩
  rw [hj] at h2 ⊢
  simp only [Nat.add_sub_cancel] at h2
  rw [harmonic_succ]
  have h3 := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at h3
  push_cast
  linarith

theorem a_tendsto : Tendsto A226187 atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro N
  rw [Filter.eventually_atTop]
  refine ⟨⌈3 * (harmonic N : ℚ)⌉₊, fun n hn => ?_⟩
  by_contra hc
  have hlt : A226187 n ≤ N := by omega
  have hm : harmonic (A226187 n) ≤ harmonic N := harmonic_monotone hlt
  have hs := a_spec n
  have hc' : (3 * harmonic N : ℚ) ≤ n :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  linarith

/-- The conjecture: a(n+1)/a(n) → exp(1/3) = 1.3956... -/
theorem A226187_ratio :
    Tendsto (fun n => (A226187 (n + 1) : ℝ) / A226187 n) atTop
      (𝓝 (Real.exp (1 / 3))) := by
  have hA : Tendsto (fun n => (A226187 n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp a_tendsto
  have hinv : Tendsto (fun n => ((A226187 n : ℝ))⁻¹) atTop (𝓝 0) :=
    hA.inv_tendsto_atTop
  have hγ : Tendsto (fun n => (harmonic (A226187 n) : ℝ) - Real.log (A226187 n)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp a_tendsto
  have he : Tendsto (fun n : ℕ => (harmonic (A226187 n) : ℝ) - (n : ℝ) / 3) atTop
      (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
      (fun n => ?_) (fun n => ?_)
    · have h := (Rat.cast_lt (K := ℝ)).mpr (a_spec n)
      push_cast at h
      dsimp only
      linarith
    · have h := a_upper n
      dsimp only
      linarith
  have hL : Tendsto (fun n : ℕ => Real.log (A226187 n) - (n : ℝ) / 3) atTop
      (𝓝 (0 - Real.eulerMascheroniConstant)) := by
    refine (he.sub hγ).congr (fun n => ?_)
    ring
  have hL1 := hL.comp (tendsto_add_atTop_nat 1)
  have hD : Tendsto (fun n => Real.log (A226187 (n + 1)) - Real.log (A226187 n)) atTop
      (𝓝 (1 / 3)) := by
    have h := (hL1.sub hL).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop _)
    have e : (0 - Real.eulerMascheroniConstant) - (0 - Real.eulerMascheroniConstant) + 1 / 3
        = (1 / 3 : ℝ) := by ring
    rw [e] at h
    refine h.congr (fun n => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring
  have hE := (Real.continuous_exp.tendsto _).comp hD
  refine hE.congr (fun n => ?_)
  have p1 : (0 : ℝ) < A226187 (n + 1) := Nat.cast_pos.mpr (by have := a_pos (n + 1); omega)
  have p0 : (0 : ℝ) < A226187 n := Nat.cast_pos.mpr (by have := a_pos n; omega)
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log p1, Real.exp_log p0]
