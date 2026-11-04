/-
OEIS A226188, Mathlib proof.

a(n) is the least positive k with H_k = 1 + 1/2 + ... + 1/k > 2n/3.
Since H_0 = 0, the least k ≥ 0 with that property is automatically positive,
so a(n) is characterised by `IsLeast {k | ... < harmonic k} (a n)`.

Main theorem `A226188_main`: for this a, a(n+1)/a(n) → exp(2/3) = 1.9477...
(`Filter.Tendsto ... atTop (𝓝 (Real.exp ...))`), the README result.

Proof (`A226188_ratio`, for any constant c > 0 in place of the slope): with
a = a(n), H_a - 1/a ≤ n c < H_a; H_a ≤ 1 + log a forces a(n) → ∞, and
Mathlib's `Real.tendsto_harmonic_sub_log` (H_k - log k → γ) then gives
n c - log a(n) → γ, so log a(n+1) - log a(n) → c.

Not checked: nothing.
-/
import Mathlib

open Filter Topology Real

theorem A226188_exists (c : ℝ) (n : ℕ) : ∃ k : ℕ, (n : ℝ) * c < harmonic k := by
  refine ⟨⌈Real.exp ((n : ℝ) * c)⌉₊, ?_⟩
  have h1 := log_add_one_le_harmonic ⌈Real.exp ((n : ℝ) * c)⌉₊
  have h2 : Real.exp ((n : ℝ) * c) < ((⌈Real.exp ((n : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (Real.exp ((n : ℝ) * c))]
  have h3 : (n : ℝ) * c < Real.log ((⌈Real.exp ((n : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact h2
  linarith

open Classical in
/-- a(n): the least k with H_k > n c (positive when c > 0). -/
noncomputable def A226188_thr (c : ℝ) (n : ℕ) : ℕ := Nat.find (A226188_exists c n)

theorem A226188_ratio (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n => (A226188_thr c (n + 1) : ℝ) / A226188_thr c n) atTop (𝓝 (Real.exp c)) := by
  classical
  set a := A226188_thr c with ha
  have hspec : ∀ n : ℕ, (n : ℝ) * c < harmonic (a n) := fun n => Nat.find_spec (A226188_exists c n)
  have hpos : ∀ n, 1 ≤ a n := by
    intro n
    by_contra h
    have h0 : a n = 0 := by omega
    have := hspec n
    rw [h0] at this
    simp only [harmonic_zero, Rat.cast_zero] at this
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmin : ∀ n, (harmonic (a n) : ℝ) - 1 / (a n) ≤ (n : ℝ) * c := by
    intro n
    obtain ⟨m, hm⟩ : ∃ m, a n = m + 1 := ⟨a n - 1, by have := hpos n; omega⟩
    have hlt : m < a n := by omega
    have := not_lt.mp (Nat.find_min (A226188_exists c n) (show m < Nat.find (A226188_exists c n) from hlt))
    rw [hm, harmonic_succ]
    push_cast
    simp only [one_div]
    linarith
  have hapos : ∀ n, (0 : ℝ) < a n := fun n => by exact_mod_cast hpos n
  -- a(n) → ∞, since n c < H_(a n) ≤ 1 + log a(n) ≤ a(n).
  --
  have hreal : Tendsto (fun n => (a n : ℝ)) atTop atTop := by
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * c - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
    refine tendsto_atTop_mono (fun n => ?_) hlin
    have h1 := hspec n
    have h2 := harmonic_le_one_add_log (a n)
    have h3 := Real.add_one_le_exp (Real.log (a n))
    rw [Real.exp_log (hapos n)] at h3
    linarith
  have hnat : Tendsto a atTop atTop := tendsto_natCast_atTop_iff.mp hreal
  have hL : Tendsto (fun n => (harmonic (a n) : ℝ) - Real.log (a n)) atTop
      (𝓝 eulerMascheroniConstant) := tendsto_harmonic_sub_log.comp hnat
  have hinv : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hreal
  -- e(n) = n c - log a(n) → γ.
  --
  set e := fun n : ℕ => (n : ℝ) * c - Real.log (a n) with he
  have hlow : Tendsto (fun n => (harmonic (a n) : ℝ) - Real.log (a n) - 1 / (a n)) atTop
      (𝓝 eulerMascheroniConstant) := by simpa using hL.sub hinv
  have he_t : Tendsto e atTop (𝓝 eulerMascheroniConstant) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hL (fun n => ?_) (fun n => ?_)
    · have := hmin n
      simp only [he]
      linarith
    · have := hspec n
      simp only [he]
      linarith
  have he1 : Tendsto (fun n => e (n + 1)) atTop (𝓝 eulerMascheroniConstant) :=
    he_t.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n => c - e (n + 1) + e n) atTop
      (𝓝 (c - eulerMascheroniConstant + eulerMascheroniConstant)) :=
    (tendsto_const_nhds.sub he1).add he_t
  rw [sub_add_cancel] at hdiff
  have hexp := (Real.continuous_exp.tendsto c).comp hdiff
  refine hexp.congr (fun n => ?_)
  simp only [Function.comp, he]
  rw [show c - ((((n + 1 : ℕ) : ℝ)) * c - Real.log (a (n + 1))) + ((n : ℝ) * c - Real.log (a n)) =
      Real.log (a (n + 1)) - Real.log (a n) by push_cast; ring]
  rw [Real.exp_sub, Real.exp_log (hapos _), Real.exp_log (hapos _)]

theorem A226188_main (a : ℕ → ℕ)
    (ha : ∀ n : ℕ, IsLeast {k : ℕ | 2 * (n : ℝ) / 3 < harmonic k} (a n)) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 (Real.exp (2 / 3))) := by
  classical
  have hc : (0 : ℝ) < 2 / 3 := by positivity
  have heq : a = A226188_thr (2 / 3) := by
    funext n
    have hset : {k : ℕ | 2 * (n : ℝ) / 3 < harmonic k} = {k : ℕ | (n : ℝ) * (2 / 3) < harmonic k} := by
      ext k
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> [skip; skip] <;> (convert h using 1; ring)
    have han := ha n
    rw [hset] at han
    refine han.unique ⟨Nat.find_spec (A226188_exists (2 / 3) n), fun k hk => ?_⟩
    exact Nat.find_min' (A226188_exists (2 / 3) n) hk
  rw [heq]
  exact A226188_ratio _ hc
