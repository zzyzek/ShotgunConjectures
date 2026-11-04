/-
OEIS A139043 (a(n) = sum of the composite numbers ≤ 10^n), conjecture
(C. Hilliard 2008): 10^n(10^n+1)/2 − 1 − (10^n)^2/(2 log(10^n) − 1) → a(n),
with the parenthetical claim (10^n)^2/(2 log(10^n) − 1) → sum of primes < 10^n.

What is checked here: the main statement in the ratio reading.
Main theorem `A139043_ratio`: with x = 10^n,
a(n) = Σ_{c ≤ x, c ≥ 2 not prime} c and
approx(n) = x(x+1)/2 − 1 − x²/(2 log x − 1),
a(n)/approx(n) → 1.  Proof: a(n) = x(x+1)/2 − 1 − S(x) with S(x) the sum of
primes ≤ x, S(x) ≤ x·π(x), and π(x)/x → 0 (Chebyshev's bound in Mathlib), so
both a(n) and approx(n) are x²/2 + o(x²).

Not checked here (README result, other parts): the parenthetical statement
S(x) ~ x²/(2 log x − 1) (prime number theorem, not in Mathlib), and the
failure of the difference reading for both statements (PNT with error term).
-/
import Mathlib

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
