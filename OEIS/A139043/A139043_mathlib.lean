import Mathlib
import PNTPlus.Consequences
import PNTPlus.StrongPNT

/-
OEIS A139043 (a(n) = sum of the composite numbers ≤ 10^n), conjecture
(C. Hilliard 2008): 10^n(10^n+1)/2 − 1 − (10^n)^2/(2 log(10^n) − 1) → a(n),
with the parenthetical claim (10^n)^2/(2 log(10^n) − 1) → sum of primes < 10^n.

What is checked here: both statements in both readings (ratio: true; difference: false).
* `A139043_ratio`: with x = 10^n, a(n) = Σ_{c ≤ x, c ≥ 2 not prime} c and
  approx(n) = x(x+1)/2 − 1 − x²/(2 log x − 1), a(n)/approx(n) → 1.  Proof: a(n) =
  x(x+1)/2 − 1 − S(x) with S(x) the sum of primes ≤ x, S(x) ≤ x·π(x), and π(x)/x → 0
  (Chebyshev's bound in Mathlib), so both are x²/2 + o(x²).
* `A139043_primes_ratio`: S(10^n) / ((10^n)²/(2 log 10^n − 1)) → 1 (S counts primes ≤ x;
  for n ≥ 1, x = 10^n is not prime, so this is the sum of primes < x). Route (namespace
  A139043PNT): θ(x) ~ x (`chebyshev_asymptotic`, vendored PrimeNumberTheoremAnd in
  lib/PNTPlus); summation by parts T(N) = Σ_{p≤N} p log p = N θ(N) − Σ_{k<N} θ(k), so
  T(N) = N²/2 + o(N²); then T(N)/log N ≤ S(N) ≤ (N+1) N^{1−η} + T(N)/((1−η) log N)
  for every η in (0, 1).

* `A139043_primes_difference`, `A139043_main_difference` (difference reading, false):
  S(10^n) − x²/(2 log x − 1) → +∞, and approx(n) − a(n) is the same quantity. Route
  (namespace A139043Diff): θ(x) − x = O(x/log⁴ x) from `StrongPNT` (lib/PNTPlus) and
  Mathlib's ψ − θ = O(√x); Abel summation S(N) = Σ_{n≤N} n/log n + B(N) N/log N
  − Σ_{k<N} B(k)(f(k+1) − f(k)) with B(k) = θ(k) − k − 1, f(n) = n/log n; the mean value
  theorem for F(t) = t²/(2 log t) + t²/(4 log² t) + t²/(4 log³ t), whose derivative is
  t/log t − 3t/(4 log⁴ t), gives Σ_{n≤N} n/log n ≥ F(N) − F(3); and
  F(N) − N²/(2 log N − 1) = N²/(8 log³ N) − N²/(8 log³ N (2 log N − 1)).

Not checked here: that the Lean statements match the OEIS text.
-/

open Filter Topology Real Finset

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

/-- Sum of the composite numbers ≤ x. -/
def compSum (x : ℕ) : ℕ := ∑ c ∈ (Icc 2 x).filter (fun c => ¬ c.Prime), c
/-- Sum of the primes ≤ x. -/
def primeSum (x : ℕ) : ℕ := ∑ c ∈ (Icc 2 x).filter (fun c => c.Prime), c

noncomputable def approx (x : ℕ) : ℝ :=
  (x : ℝ) * (x + 1) / 2 - 1 - (x : ℝ) ^ 2 / (2 * log x - 1)

lemma sum_Icc_two (x : ℕ) (hx : 1 ≤ x) : ((∑ c ∈ Icc 2 x, c : ℕ) : ℝ) = (x : ℝ) * (x + 1) / 2 - 1 := by
  induction x, hx using Nat.le_induction with
  | base => simp
  | succ x hx ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast at ih ⊢
    rw [ih]; ring

lemma comp_add_prime (x : ℕ) : compSum x + primeSum x = ∑ c ∈ Icc 2 x, c := by
  unfold compSum primeSum
  rw [add_comm]; exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma primeSum_le (x : ℕ) : primeSum x ≤ x * Nat.primeCounting x := by
  unfold primeSum
  have hcard : ((Icc 2 x).filter (fun c => c.Prime)).card ≤ Nat.primeCounting x := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply card_le_card
    intro c hc
    simp only [mem_filter, mem_Icc] at hc
    exact Nat.mem_primesLE.2 ⟨hc.1.2, hc.2⟩
  calc ∑ c ∈ (Icc 2 x).filter (fun c => c.Prime), c
      ≤ ∑ c ∈ (Icc 2 x).filter (fun c => c.Prime), x := by
        apply sum_le_sum; intro c hc; simp only [mem_filter, mem_Icc] at hc; exact hc.1.2
    _ = ((Icc 2 x).filter (fun c => c.Prime)).card * x := by rw [sum_const, smul_eq_mul]
    _ ≤ Nat.primeCounting x * x := Nat.mul_le_mul_right _ hcard
    _ = x * Nat.primeCounting x := by ring

lemma half_limit :
    Tendsto (fun x : ℕ => ((x : ℝ) * (x + 1) / 2 - 1) / (x : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun x : ℕ => (1 / 2 : ℝ) + (1 / 2) * (1 / x) - (1 / x) ^ 2) atTop
      (𝓝 (1 / 2 + 1 / 2 * 0 - 0 ^ 2)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul h1)).sub (h1.pow 2))
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at h2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : (x : ℝ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  field_simp

lemma compSum_limit :
    Tendsto (fun x : ℕ => (compSum x : ℝ) / (x : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have hS : Tendsto (fun x : ℕ => (primeSum x : ℝ) / (x : ℝ) ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      primeCounting_div_tendsto_zero
    · exact Eventually.of_forall fun x => by positivity
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      have := primeSum_le x
      have h' : (primeSum x : ℝ) ≤ x * Nat.primeCounting x := by exact_mod_cast this
      rw [div_le_div_iff₀ (by positivity) hx0]
      nlinarith
  have h := half_limit.sub hS
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have e := comp_add_prime x
  have e' : (compSum x : ℝ) = (x : ℝ) * (x + 1) / 2 - 1 - primeSum x := by
    rw [← sum_Icc_two x hx, ← e]; push_cast; ring
  rw [e']; ring

lemma approx_limit : Tendsto (fun x : ℕ => approx x / (x : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have hL : Tendsto (fun x : ℕ => 2 * log (x : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have hinv : Tendsto (fun x : ℕ => 1 / (2 * log (x : ℝ) - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have h := half_limit.sub hinv
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  have hx2 : (x : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hq : (x : ℝ) ^ 2 / (2 * log (x : ℝ) - 1) / (x : ℝ) ^ 2 = 1 / (2 * log (x : ℝ) - 1) := by
    rw [div_div, mul_comm (2 * log (x : ℝ) - 1), ← div_div, div_self hx2]
  show _ = approx x / (x : ℝ) ^ 2
  unfold approx
  rw [sub_div ((x : ℝ) * (x + 1) / 2 - 1), hq]

theorem ratio_limit : Tendsto (fun x : ℕ => (compSum x : ℝ) / approx x) atTop (𝓝 1) := by
  have h := compSum_limit.div approx_limit (by norm_num)
  rw [div_self (by norm_num)] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : (x : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by omega : x ≠ 0))
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hx0]

theorem A139043_ratio :
    Tendsto (fun n : ℕ => (compSum (10 ^ n) : ℝ) / approx (10 ^ n)) atTop (𝓝 1) :=
  ratio_limit.comp (tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) (by norm_num))

open Asymptotics

namespace A139043PNT

/-- Sum of the primes in 0..N, as a real number. -/
noncomputable def pS (N : ℕ) : ℝ := ∑ c ∈ range (N + 1), if c.Prime then (c : ℝ) else 0
/-- Sum of p log p over the primes in 0..N. -/
noncomputable def pT (N : ℕ) : ℝ :=
  ∑ c ∈ range (N + 1), if c.Prime then (c : ℝ) * log (c : ℝ) else 0
/-- Chebyshev's theta at N, written over 0..N. -/
noncomputable def pTheta (N : ℕ) : ℝ := ∑ c ∈ range (N + 1), if c.Prime then log (c : ℝ) else 0

theorem pTheta_eq (N : ℕ) : pTheta N = Chebyshev.theta N := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, pTheta, Nat.primesLE, Nat.primesBelow, Finset.sum_filter]

/-- Summation by parts. -/
theorem pT_abel (N : ℕ) : pT N = N * pTheta N - ∑ k ∈ range N, pTheta k := by
  induction N with
  | zero => simp [pT, pTheta, Nat.not_prime_zero]
  | succ n ih =>
    have h1 : pT (n + 1) = pT n +
        (if (n + 1).Prime then ((n + 1 : ℕ) : ℝ) * log ((n + 1 : ℕ) : ℝ) else 0) := by
      simp only [pT]; rw [Finset.sum_range_succ]
    have h2 : pTheta (n + 1) = pTheta n + (if (n + 1).Prime then log ((n + 1 : ℕ) : ℝ) else 0) := by
      simp only [pTheta]; rw [Finset.sum_range_succ]
    rw [h1, h2, ih, Finset.sum_range_succ]
    split_ifs <;> push_cast <;> ring

theorem sum_range_cast (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem pTheta_isLittleO : (fun k : ℕ => pTheta k - k) =o[atTop] (fun k : ℕ => (k : ℝ)) := by
  have h := chebyshev_asymptotic.comp_tendsto tendsto_natCast_atTop_atTop
  refine h.isLittleO.congr (fun k => ?_) (fun k => ?_) <;> simp [pTheta_eq]


theorem sum_range_tendsto : Tendsto (fun n : ℕ => ∑ i ∈ range n, (i : ℝ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + (-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1 : ℝ) tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono (fun n => ?_) h
  rw [sum_range_cast]
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · have : (0 : ℝ) ≤ n := n.cast_nonneg
    push_cast; nlinarith

theorem pT_isLittleO :
    (fun N : ℕ => pT N - (N : ℝ) ^ 2 / 2) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2) := by
  have hs := pTheta_isLittleO.sum_range (fun k => Nat.cast_nonneg k) sum_range_tendsto
  have hO : (fun n : ℕ => ∑ i ∈ range n, (i : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) ^ 2) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [sum_range_cast, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2), abs_le]
    rcases n with _ | n
    · norm_num
    · have : (0 : ℝ) ≤ n := n.cast_nonneg
      push_cast
      constructor <;> nlinarith
  have h1 := hs.trans_isBigO hO
  have h2 : (fun N : ℕ => (N : ℝ) * (pTheta N - N)) =o[atTop] (fun N : ℕ => (N : ℝ) * N) :=
    (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop).mul_isLittleO pTheta_isLittleO
  have h2' : (fun N : ℕ => (N : ℝ) * (pTheta N - N)) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2) :=
    h2.congr_right (fun N => by ring)
  have h3 : (fun N : ℕ => (N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2) := by
    have := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (by norm_num : 1 < 2)).comp_tendsto
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h4 := (h2'.sub h1).add (h3.const_mul_left (1 / 2))
  refine h4.congr_left (fun N => ?_)
  rw [Finset.sum_sub_distrib, pT_abel, sum_range_cast]
  ring

theorem pT_tendsto : Tendsto (fun N : ℕ => pT N / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have h := pT_isLittleO.tendsto_div_nhds_zero.add_const (1 / 2)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by omega : N ≠ 0))
  field_simp
  ring

/-- Lower comparison: log p ≤ log N for p ≤ N. -/
theorem pT_le (N : ℕ) : pT N ≤ pS N * log N := by
  rw [pT, pS, Finset.sum_mul]
  refine Finset.sum_le_sum (fun c hc => ?_)
  have hcN : c ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
  split_ifs with hp
  · have hc0 : (0 : ℝ) < c := by exact_mod_cast hp.pos
    exact mul_le_mul_of_nonneg_left (log_le_log hc0 (by exact_mod_cast hcN)) hc0.le
  · simp

/-- Upper comparison: primes above N / N^η have log p > (1 - η) log N. -/
theorem pS_le (N : ℕ) (hN : 2 ≤ N) {η : ℝ} (hη : η < 1) :
    pS N ≤ (N + 1) * ((N : ℝ) / (N : ℝ) ^ η) + pT N / ((1 - η) * log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hK : 0 < (1 - η) * log N := mul_pos (by linarith) hlogN
  set y : ℝ := (N : ℝ) / (N : ℝ) ^ η with hy
  have hy0 : 0 ≤ y := by positivity
  have hlogy : log y = (1 - η) * log N := by
    rw [hy, log_div hN0.ne' (by positivity), log_rpow hN0]; ring
  have key : ∀ c ∈ range (N + 1), (if c.Prime then (c : ℝ) else 0) ≤
      y + (if c.Prime then (c : ℝ) * log (c : ℝ) else 0) / ((1 - η) * log N) := by
    intro c _
    split_ifs with hp
    · have hc0 : (0 : ℝ) < c := by exact_mod_cast hp.pos
      have hlc : 0 ≤ log (c : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
      by_cases hcy : (c : ℝ) ≤ y
      · have : 0 ≤ (c : ℝ) * log c / ((1 - η) * log N) := by positivity
        linarith
      · replace hcy := not_le.mp hcy
        have hl : (1 - η) * log N < log c := by
          rw [← hlogy]; exact log_lt_log (by positivity) hcy
        have : (c : ℝ) ≤ (c : ℝ) * log c / ((1 - η) * log N) := by
          rw [le_div_iff₀ hK]
          exact mul_le_mul_of_nonneg_left hl.le hc0.le
        linarith
    · simp only [zero_div, add_zero]; exact hy0
  calc pS N ≤ ∑ c ∈ range (N + 1), (y + (if c.Prime then (c : ℝ) * log (c : ℝ) else 0) /
        ((1 - η) * log N)) := Finset.sum_le_sum key
    _ = (N + 1) * y + pT N / ((1 - η) * log N) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, pT, Finset.sum_div,
          nsmul_eq_mul]
        push_cast; ring

theorem log_div_rpow_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ => log (N : ℝ) / (N : ℝ) ^ η) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop hη).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

theorem succ_div_tendsto : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => (1 : ℝ) + 1 / N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp

/-- Sum of the primes up to N is asymptotic to N^2 / (2 log N). -/
theorem pS_tendsto : Tendsto (fun N : ℕ => pS N * log N / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [(tendsto_order.1 pT_tendsto).1 a ha, eventually_ge_atTop 1] with N h1 hN
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      positivity
    calc a < pT N / (N : ℝ) ^ 2 := h1
      _ ≤ pS N * log N / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right (pT_le N) hN2.le
  · intro b hb
    set η : ℝ := (2 * b - 1) / (4 * b) with hηdef
    have hb0 : 0 < b := by linarith
    have hη0 : 0 < η := by rw [hηdef]; apply div_pos <;> linarith
    have hη1 : η < 1 := by rw [hηdef, div_lt_one (by linarith)]; linarith
    have hbη : b * (1 - η) = (2 * b + 1) / 4 := by rw [hηdef]; field_simp; ring
    have hlim : (1 / 2) / (1 - η) < b := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    have hu : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N * (log (N : ℝ) / (N : ℝ) ^ η) +
        pT N / (N : ℝ) ^ 2 / (1 - η)) atTop (𝓝 (1 * 0 + (1 / 2) / (1 - η))) :=
      (succ_div_tendsto.mul (log_div_rpow_tendsto hη0)).add (pT_tendsto.div_const _)
    rw [mul_zero, zero_add] at hu
    filter_upwards [(tendsto_order.1 hu).2 b hlim, eventually_ge_atTop 2] with N h1 hN
    refine lt_of_le_of_lt ?_ h1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
    have hS' := mul_le_mul_of_nonneg_right (pS_le N hN hη1) hlogN.le
    have h1η : (1 - η) ≠ 0 := by linarith
    have hpow : (N : ℝ) ^ η ≠ 0 := by positivity
    calc pS N * log N / (N : ℝ) ^ 2
        ≤ ((N + 1) * ((N : ℝ) / (N : ℝ) ^ η) + pT N / ((1 - η) * log N)) * log N /
            (N : ℝ) ^ 2 := div_le_div_of_nonneg_right hS' (by positivity)
      _ = ((N : ℝ) + 1) / N * (log (N : ℝ) / (N : ℝ) ^ η) + pT N / (N : ℝ) ^ 2 / (1 - η) := by
          field_simp

theorem primeSum_eq_pS (x : ℕ) : (primeSum x : ℝ) = pS x := by
  rw [primeSum, pS]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_subset (fun c hc => ?_) (fun c hc hnot => ?_)
  · rw [Finset.mem_Icc] at hc
    exact Finset.mem_range.mpr (by omega)
  · have h1 := Finset.mem_range.mp hc
    rw [Finset.mem_Icc] at hnot
    have hc2 : c < 2 := by omega
    have hnp : ¬ c.Prime := fun hp => absurd hp.two_le (by omega)
    simp [hnp]

/-- The sum of the primes up to x divided by x^2 / (2 log x - 1) tends to 1. -/
theorem primeSum_ratio_limit :
    Tendsto (fun x : ℕ => (primeSum x : ℝ) / ((x : ℝ) ^ 2 / (2 * log x - 1))) atTop (𝓝 1) := by
  have hL : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun x : ℕ => 2 - 1 / log (x : ℝ)) atTop (𝓝 (2 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hL)
  have h := pS_tendsto.mul h2
  have e : (1 : ℝ) / 2 * (2 - 0) = 1 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog2 : (1 : ℝ) / 2 < log x := by
    have h2l := Real.log_two_gt_d9
    have : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) (by exact_mod_cast hx)
    linarith
  have hlog : log (x : ℝ) ≠ 0 := by linarith
  have hden : 2 * log (x : ℝ) - 1 ≠ 0 := by linarith
  rw [primeSum_eq_pS]
  field_simp

/-- **A139043, parenthetical claim (ratio reading)**: with x = 10^n, the sum of the
primes ≤ x divided by x^2 / (2 log x - 1) tends to 1. -/
theorem A139043_primes_ratio :
    Tendsto (fun n : ℕ => (primeSum (10 ^ n) : ℝ) /
      (((10 ^ n : ℕ) : ℝ) ^ 2 / (2 * log ((10 ^ n : ℕ) : ℝ) - 1))) atTop (𝓝 1) :=
  primeSum_ratio_limit.comp (tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) (by norm_num))

namespace A139043Diff

/-- Third-order antiderivative of t / log t, up to a term of order t / log^4 t. -/
noncomputable def F (t : ℝ) : ℝ := t ^ 2 / (2 * log t) + t ^ 2 / (4 * log t ^ 2) + t ^ 2 / (4 * log t ^ 3)

theorem hasDerivAt_F {t : ℝ} (ht : 1 < t) :
    HasDerivAt F (t / log t - 3 * t / (4 * log t ^ 4)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (log_pos ht).ne'
  have hL : HasDerivAt log t⁻¹ t := hasDerivAt_log ht0
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have d1 := h2.div (hL.const_mul 2) (by positivity)
  have d2 := h2.div ((hL.pow 2).const_mul 4) (by simp [Pi.pow_apply, hl])
  have d3 := h2.div ((hL.pow 3).const_mul 4) (by simp [Pi.pow_apply, hl])
  have := (d1.add d2).add d3
  have e : F = ((fun x : ℝ => x ^ 2) / fun y => 2 * log y) +
      ((fun x : ℝ => x ^ 2) / fun y => 4 * (log ^ 2) y) +
      ((fun x : ℝ => x ^ 2) / fun y => 4 * (log ^ 3) y) := by
    funext x
    simp [F, Pi.div_apply, Pi.pow_apply]
  rw [e]
  convert this using 1
  simp only [Pi.pow_apply]
  norm_num
  field_simp
  ring

theorem self_div_log_le {c n : ℝ} (hc : 3 ≤ c) (hcn : c ≤ n) : c / log c ≤ n / log n := by
  have he : exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hlc : 0 < log c := log_pos (by linarith)
  have hln : 0 < log n := log_pos (by linarith)
  have h := log_div_self_antitoneOn (Set.mem_Ici.mpr (he.trans hc))
    (Set.mem_Ici.mpr (he.trans (hc.trans hcn))) hcn
  simp only at h
  rw [div_le_div_iff₀ hlc hln]
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  linarith

theorem F_step {n : ℝ} (hn : 4 ≤ n) : F n - F (n - 1) ≤ n / log n := by
  have hab : n - 1 < n := by linarith
  have hd : ∀ x ∈ Set.Icc (n - 1) n, HasDerivAt F (x / log x - 3 * x / (4 * log x ^ 4)) x :=
    fun x hx => hasDerivAt_F (by linarith [hx.1])
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope F
    (fun x => x / log x - 3 * x / (4 * log x ^ 4)) hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have hc3 : 3 ≤ c := by linarith [hc.1]
  have hlc : 0 < log c := log_pos (by linarith)
  rw [sub_sub_cancel, div_one] at hcd
  rw [← hcd]
  have : 0 ≤ 3 * c / (4 * log c ^ 4) := by positivity
  have := self_div_log_le hc3 hc.2.le
  linarith

theorem F_le_sum (N : ℕ) (hN : 3 ≤ N) :
    F N - F 3 ≤ ∑ n ∈ range (N + 1), (n : ℝ) / log n := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Nat.cast_ofNat, sub_self]
    exact Finset.sum_nonneg fun n _ => div_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg n)
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have h := F_step (n := ((N + 1 : ℕ) : ℝ)) (by push_cast; exact_mod_cast (by omega : 4 ≤ N + 1))
    have e : ((N + 1 : ℕ) : ℝ) - 1 = N := by push_cast; ring
    rw [e] at h
    linarith

/-- θ(x) − x = O(x / log⁴ x), from the de la Vallée Poussin error term (`StrongPNT`). -/
theorem theta_err :
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x => x / log x ^ 4) := by
  obtain ⟨c, hc, hS⟩ := StrongPNT
  have hE : (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 2))) =O[atTop]
      (fun x => x / log x ^ 4) := by
    have hu : Tendsto (fun x : ℝ => c * log x ^ ((1 : ℝ) / 2)) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop).const_mul_atTop hc
    have h0 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp hu
    refine IsBigO.of_bound (c ^ 8)⁻¹ ?_
    filter_upwards [(tendsto_order.1 h0).2 1 one_pos, eventually_gt_atTop 1] with x hx hx1
    simp only [Function.comp_apply] at hx
    have hl : 0 < log x := log_pos hx1
    have hx0 : 0 < x := by linarith
    have hu8 : (log x ^ ((1 : ℝ) / 2)) ^ 8 = log x ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]; norm_num
    rw [mul_pow, hu8] at hx
    have hK : 0 < c ^ 8 * log x ^ 4 := by positivity
    have hexp : exp (-c * log x ^ ((1 : ℝ) / 2)) ≤ 1 / (c ^ 8 * log x ^ 4) := by
      rw [le_div_iff₀ hK, neg_mul]; linarith
    rw [norm_mul, Real.norm_of_nonneg hx0.le, Real.norm_of_nonneg (exp_pos _).le,
      Real.norm_of_nonneg (by positivity : 0 ≤ x / log x ^ 4)]
    calc x * exp (-c * log x ^ ((1 : ℝ) / 2)) ≤ x * (1 / (c ^ 8 * log x ^ 4)) :=
          mul_le_mul_of_nonneg_left hexp hx0.le
      _ = (c ^ 8)⁻¹ * (x / log x ^ 4) := by field_simp
  have hSq : (fun x : ℝ => √x) =O[atTop] (fun x => x / log x ^ 4) := by
    have h := isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
    refine IsBigO.of_bound 1 ?_
    filter_upwards [h.bound one_pos, eventually_gt_atTop 1] with x hx hx1
    have hl : 0 < log x := log_pos hx1
    have hx0 : 0 < x := by linarith
    have e4 : log x ^ (4 : ℝ) = log x ^ 4 := by exact_mod_cast Real.rpow_natCast (log x) 4
    rw [e4, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      ← Real.sqrt_eq_rpow] at hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity), one_mul,
      le_div_iff₀ (by positivity)]
    calc √x * log x ^ 4 ≤ √x * √x := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)
      _ = x := Real.mul_self_sqrt hx0.le
  have h := (hS.trans hE).sub (Chebyshev.isBigO_psi_sub_theta_sqrt.trans hSq)
  refine h.congr_left (fun x => ?_)
  simp only [Pi.sub_apply, id]
  ring

noncomputable def f (n : ℕ) : ℝ := (n : ℝ) / log n
noncomputable def b (n : ℕ) : ℝ := (if n.Prime then log (n : ℝ) else 0) - 1
noncomputable def B (k : ℕ) : ℝ := ∑ n ∈ range (k + 1), b n

theorem B_eq (k : ℕ) : B k = Chebyshev.theta k - (k + 1) := by
  rw [B, Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  simp [b, Finset.sum_sub_distrib]

theorem abel (N : ℕ) : ∑ n ∈ range (N + 1), b n * f n =
    B N * f N - ∑ k ∈ range N, B k * (f (k + 1) - f k) := by
  induction N with
  | zero => simp [B]
  | succ N ih =>
    have hB : B (N + 1) = B N + b (N + 1) := by simp only [B]; rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => B k * (f (k + 1) - f k)), hB]
    ring

theorem sum_bf (N : ℕ) :
    ∑ n ∈ range (N + 1), b n * f n = pS N - ∑ n ∈ range (N + 1), f n := by
  rw [pS, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [b, f]
  split_ifs with hp
  · have hl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp
  · ring

theorem f_step (k : ℕ) (hk : 3 ≤ k) : 0 ≤ f (k + 1) - f k ∧ f (k + 1) - f k ≤ 1 := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hlk : 1 ≤ log (k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlk1 : log (k : ℝ) ≤ log ((k + 1 : ℕ) : ℝ) :=
    log_le_log (by linarith) (by push_cast; linarith)
  constructor
  · have := self_div_log_le hk3 (by push_cast; linarith : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
    simp only [f]; linarith
  · simp only [f]
    have h1 : ((k + 1 : ℕ) : ℝ) / log ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / log (k : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hlk1
    have h2 : ((k + 1 : ℕ) : ℝ) / log (k : ℝ) - (k : ℝ) / log k = 1 / log k := by
      push_cast; field_simp; ring
    have h3 : 1 / log (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hlk
    linarith

/-- Splitting at √N: k / log⁴ k ≤ √N + 16 N / log⁴ N for 3 ≤ k ≤ N. -/
theorem split_bound {k N : ℕ} (hk : 3 ≤ k) (hkN : k ≤ N) :
    (k : ℝ) / log k ^ 4 ≤ √(N : ℝ) + 16 * (N / log N ^ 4) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hlk : 1 ≤ log (k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlN : 0 < log (N : ℝ) := log_pos (by linarith)
  have hA : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hB : 0 ≤ 16 * ((N : ℝ) / log N ^ 4) := by positivity
  by_cases hs : (k : ℝ) ≤ √(N : ℝ)
  · have : (k : ℝ) / log k ^ 4 ≤ k := div_le_self (by linarith) (one_le_pow₀ hlk)
    linarith
  · replace hs := not_le.mp hs
    have hl2 : log (N : ℝ) / 2 ≤ log (k : ℝ) := by
      have h1 : log (√(N : ℝ)) = log (N : ℝ) / 2 := by
        rw [Real.log_sqrt (by linarith)]
      rw [← h1]; exact log_le_log (Real.sqrt_pos.mpr (by linarith)) hs.le
    have hp : (log (N : ℝ) / 2) ^ 4 ≤ log (k : ℝ) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity) hl2
    have : (k : ℝ) / log k ^ 4 ≤ 16 * ((N : ℝ) / log N ^ 4) := by
      rw [div_le_iff₀ (by positivity)]
      calc (k : ℝ) ≤ N := hkN'
        _ = 16 * ((N : ℝ) / log N ^ 4) * (log (N : ℝ) / 2) ^ 4 := by field_simp; ring
        _ ≤ 16 * ((N : ℝ) / log N ^ 4) * log (k : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left hp hB
    linarith

theorem f_nonneg (n : ℕ) : 0 ≤ f n := div_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg n)

/-- Lower bound for the sum of the primes, with explicit error terms. -/
theorem pS_lower : ∃ C A : ℝ, 0 ≤ C ∧ ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
    F N - A - N * (C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1) -
      (C * (N / log N ^ 4) + 1) * f N ≤ pS N := by
  obtain ⟨C0, hC0⟩ := theta_err.bound
  obtain ⟨X, hX⟩ := eventually_atTop.mp hC0
  set C := max C0 0 with hCdef
  set K : ℕ := max ⌈X⌉₊ 3 + 1 with hKdef
  have hBk : ∀ k : ℕ, K ≤ k → |B k| ≤ C * ((k : ℝ) / log k ^ 4) + 1 := by
    intro k hk
    have hkX : X ≤ (k : ℝ) := by
      have h1 : ⌈X⌉₊ ≤ k := by omega
      exact (Nat.le_ceil X).trans (by exact_mod_cast h1)
    have h := hX k hkX
    have hq : 0 ≤ (k : ℝ) / log k ^ 4 := by positivity
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hq] at h
    rw [B_eq]
    have h2 : C0 * ((k : ℝ) / log k ^ 4) ≤ C * ((k : ℝ) / log k ^ 4) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hq
    calc |Chebyshev.theta k - (k + 1)| ≤ |Chebyshev.theta k - k| + 1 := by
          have := abs_sub (Chebyshev.theta k - k) 1
          rw [abs_one] at this
          calc |Chebyshev.theta k - (k + 1)| = |Chebyshev.theta k - k - 1| := by ring_nf
            _ ≤ _ := this
      _ ≤ C * ((k : ℝ) / log k ^ 4) + 1 := by linarith
  set A := F 3 + ∑ k ∈ range K, |B k| * |f (k + 1) - f k| with hAdef
  refine ⟨C, A, le_max_right _ _, K, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := by omega
  have hid : pS N = ∑ n ∈ range (N + 1), f n + (B N * f N - ∑ k ∈ range N, B k * (f (k + 1) - f k)) := by
    rw [← abel, sum_bf]; ring
  have hsumf : F N - F 3 ≤ ∑ n ∈ range (N + 1), f n := F_le_sum N hN3
  have hBN := hBk N hN
  have hfN := f_nonneg N
  have hterm1 : -( (C * ((N : ℝ) / log N ^ 4) + 1) * f N) ≤ B N * f N := by
    have := neg_abs_le (B N)
    have h' : -|B N| * f N ≤ B N * f N := mul_le_mul_of_nonneg_right this hfN
    have h'' : |B N| * f N ≤ (C * ((N : ℝ) / log N ^ 4) + 1) * f N :=
      mul_le_mul_of_nonneg_right hBN hfN
    linarith
  have hbound : ∀ k ∈ Ico K N, |B k| * |f (k + 1) - f k| ≤
      C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk3 : 3 ≤ k := by omega
    have hfs := f_step k hk3
    rw [abs_of_nonneg hfs.1]
    have hsb := split_bound hk3 hk.2.le
    have hC : 0 ≤ C := le_max_right _ _
    calc |B k| * (f (k + 1) - f k) ≤ (C * ((k : ℝ) / log k ^ 4) + 1) * 1 :=
          mul_le_mul (hBk k hk.1) hfs.2 hfs.1 (by positivity)
      _ ≤ C * (√(N : ℝ) + 16 * ((N : ℝ) / log N ^ 4)) + 1 := by
          have := mul_le_mul_of_nonneg_left hsb hC
          linarith
      _ = C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1 := by ring
  have hIco : ∑ k ∈ Ico K N, |B k| * |f (k + 1) - f k| ≤
      N * (C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1) := by
    have hC : 0 ≤ C := le_max_right _ _
    have hnn : 0 ≤ C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1 := by positivity
    calc ∑ k ∈ Ico K N, |B k| * |f (k + 1) - f k|
        ≤ ∑ k ∈ Ico K N, (C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1) :=
          Finset.sum_le_sum hbound
      _ = ((N - K : ℕ) : ℝ) * (C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ N * (C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1) := by
          apply mul_le_mul_of_nonneg_right _ hnn
          exact_mod_cast Nat.sub_le N K
  have hsumB : ∑ k ∈ range N, B k * (f (k + 1) - f k) ≤
      ∑ k ∈ range K, |B k| * |f (k + 1) - f k| +
        N * (C * √(N : ℝ) + 16 * C * (N / log N ^ 4) + 1) := by
    calc ∑ k ∈ range N, B k * (f (k + 1) - f k)
        ≤ ∑ k ∈ range N, |B k| * |f (k + 1) - f k| := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [← abs_mul]; exact le_abs_self _
      _ = ∑ k ∈ range K, |B k| * |f (k + 1) - f k| + ∑ k ∈ Ico K N, |B k| * |f (k + 1) - f k| :=
          (Finset.sum_range_add_sum_Ico _ (by omega)).symm
      _ ≤ _ := by linarith
  rw [hid]
  linarith

theorem tendsto_logpow_div {n : ℕ} :
    Tendsto (fun x : ℝ => log x ^ n / x) atTop (𝓝 0) := by
  simpa using (isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero

theorem tendsto_logcube_div_sqrt : Tendsto (fun x : ℝ => log x ^ 3 / √x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [← Real.sqrt_eq_rpow]
  congr 1
  exact_mod_cast Real.rpow_natCast (log x) 3

theorem tendsto_sq_div_logcube : Tendsto (fun x : ℝ => x ^ 2 / log x ^ 3) atTop atTop := by
  have hb := (isLittleO_pow_log_id_atTop (n := 3)).bound one_pos
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [hb, eventually_gt_atTop 1] with x hx hx1
  have hl : 0 < log x := log_pos hx1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (by positivity), id, Real.norm_of_nonneg hx0.le, one_mul] at hx
  rw [id, le_div_iff₀ (by positivity)]
  nlinarith

/-- The explicit lower bound minus x²/(2 log x − 1) tends to +∞. -/
theorem R_tendsto (C A : ℝ) : Tendsto (fun x : ℝ =>
    F x - A - x * (C * √x + 16 * C * (x / log x ^ 4) + 1) - (C * (x / log x ^ 4) + 1) * (x / log x) -
      x ^ 2 / (2 * log x - 1)) atTop atTop := by
  have hL : Tendsto (fun x : ℝ => log x) atTop atTop := tendsto_log_atTop
  have t1 : Tendsto (fun x : ℝ => 1 / (8 * (2 * log x - 1))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    have h1 : Tendsto (fun x : ℝ => 2 * log x - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1 : ℝ)
        (hL.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact h1.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
  have t2 : Tendsto (fun x : ℝ => A * (log x ^ 3 / x * (1 / x))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := ((tendsto_logpow_div (n := 3)).mul h1).const_mul A
    simpa using this
  have t3 : Tendsto (fun x : ℝ => C * (log x ^ 3 / √x)) atTop (𝓝 0) := by
    simpa using tendsto_logcube_div_sqrt.const_mul C
  have t4 : Tendsto (fun x : ℝ => 16 * C / log x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
  have t5 : Tendsto (fun x : ℝ => log x ^ 3 / x) atTop (𝓝 0) := tendsto_logpow_div
  have t6 : Tendsto (fun x : ℝ => C / log x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hL)
  have t7 : Tendsto (fun x : ℝ => log x ^ 2 / x) atTop (𝓝 0) := tendsto_logpow_div
  have hg : Tendsto (fun x : ℝ => 1 / 8 - 1 / (8 * (2 * log x - 1)) - A * (log x ^ 3 / x * (1 / x)) -
      C * (log x ^ 3 / √x) - 16 * C / log x - log x ^ 3 / x - C / log x ^ 2 - log x ^ 2 / x)
      atTop (𝓝 (1 / 8 - 0 - 0 - 0 - 0 - 0 - 0 - 0)) :=
    ((((((tendsto_const_nhds.sub t1).sub t2).sub t3).sub t4).sub t5).sub t6).sub t7
  simp only [sub_zero] at hg
  have h := tendsto_sq_div_logcube.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 8) hg
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hl2 : (1 : ℝ) / 2 < log x := by
    have h2l := Real.log_two_gt_d9
    have : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) hx.le
    linarith
  have hden : 2 * log x - 1 ≠ 0 := by linarith
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = s ^ 2 :=
    ⟨√x, Real.sqrt_pos.mpr hx0, (Real.sq_sqrt hx0.le).symm⟩
  rw [Real.sqrt_sq hs0.le]
  simp only [F]
  generalize log (s ^ 2) = L at *
  have h8 : 8 * (2 * L - 1) ≠ 0 := mul_ne_zero (by norm_num) hden
  have hden2 : L * 2 - 1 ≠ 0 := by intro h; apply hden; linarith
  field_simp
  ring

/-- The sum of the primes up to N minus N²/(2 log N − 1) tends to +∞. -/
theorem diff_tendsto :
    Tendsto (fun N : ℕ => pS N - (N : ℝ) ^ 2 / (2 * log N - 1)) atTop atTop := by
  obtain ⟨C, A, _, K, hK⟩ := pS_lower
  have hR := (R_tendsto C A).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hR
  filter_upwards [eventually_ge_atTop K] with N hN
  have h := hK N hN
  simp only [Function.comp_apply, f] at h ⊢
  linarith

/-- **A139043, parenthetical claim, difference reading (false)**: with x = 10^n,
(sum of primes ≤ x) − x²/(2 log x − 1) → +∞, so it does not tend to 0. -/
theorem A139043_primes_difference :
    Tendsto (fun n : ℕ => (primeSum (10 ^ n) : ℝ) -
      ((10 ^ n : ℕ) : ℝ) ^ 2 / (2 * log ((10 ^ n : ℕ) : ℝ) - 1)) atTop atTop := by
  have h := diff_tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) (by norm_num : 1 < 10))
  refine h.congr (fun n => ?_)
  simp only [Function.comp_apply, primeSum_eq_pS]

/-- **A139043, main statement, difference reading (false)**: with x = 10^n,
approx(n) − a(n) = (sum of primes ≤ x) − x²/(2 log x − 1) → +∞. -/
theorem A139043_main_difference :
    Tendsto (fun n : ℕ => approx (10 ^ n) - (compSum (10 ^ n) : ℝ)) atTop atTop := by
  refine A139043_primes_difference.congr (fun n => ?_)
  have hx : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have e := comp_add_prime (10 ^ n)
  have e' : (compSum (10 ^ n) : ℝ) + primeSum (10 ^ n) = ((∑ c ∈ Finset.Icc 2 (10 ^ n), c : ℕ) : ℝ) := by
    exact_mod_cast e
  rw [sum_Icc_two _ hx] at e'
  simp only [approx]
  linarith
