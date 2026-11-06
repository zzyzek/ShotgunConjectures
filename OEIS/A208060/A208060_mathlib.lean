import Mathlib

/-
OEIS A208060: a(n) = 1 + 2n + 2^2 n[n/2] + 2^3 n[n/2][n/3] + ...,
[x] = floor(x).  The m-th term is 2^m * prod_{k=1..m} [n/k]; it is 0 for
m > n, so a(n) = 1 + sum_{m=1..n} 2^m prod_{k=1..m} [n/k].
Conjecture (entry text): lim a(n)^(1/n) = 2L with
log L = sum_{n>=1} log(n)/(n(n+1)).

Checked here (Lean 4.35.0, Mathlib):
* `A075885_limit`: the same for A075885 (no factor 2^m), limit L.
* `A208060_limit`: Tendsto (fun n => (a n : ℝ) ^ (1 / n)) atTop
  (𝓝 (2 * exp (∑' j, log j / (j * (j + 1))))).  The j = 0 term of the
  tsum is log 0 / 0 = 0 in Lean, so the tsum is the sum over j ≥ 1.
Route: the m = n term T = 2^n prod_{k ≤ n} [n/k] is the largest, so
T ≤ a(n) ≤ (n+1) T (`a_ge`, `a_le`); log prod_k [n/k] = sum_j d_j [n/j]
with d_j = log j - log(j-1) (`logP_eq`); [n/j] is within 1 of n/j and
sum_{j ≤ n} d_j = log n (`S_le`, `S_ge`); summation by parts turns
sum_j d_j / j into the partial sums of log j / (j(j+1)) plus log N / N
(`E_eq`).

Not checked here: nothing the statement depends on.  `a` is the OEIS
definition read with the terms m > n dropped (they vanish).
-/

open Real Filter Topology Finset

noncomputable section

/-- A208060 as defined in the OEIS entry. -/
def a (n : ℕ) : ℕ := 1 + ∑ m ∈ Icc 1 n, 2 ^ m * ∏ k ∈ Icc 1 m, n / k

/-- A075885 as defined in its OEIS entry: 1 + n + n[n/2] + n[n/2][n/3] + ... -/
def b (n : ℕ) : ℕ := 1 + ∑ m ∈ Icc 1 n, ∏ k ∈ Icc 1 m, n / k

/-- Both sequences with base c: 1 + ∑_{m ≤ n} c^m ∏_{k ≤ m} [n/k]. -/
def ag (c n : ℕ) : ℕ := 1 + ∑ m ∈ Icc 1 n, c ^ m * ∏ k ∈ Icc 1 m, n / k

lemma a_eq (n : ℕ) : a n = ag 2 n := rfl

lemma b_eq (n : ℕ) : b n = ag 1 n := by simp [b, ag]

/-- The m-th term. -/
def g (c n m : ℕ) : ℕ := c ^ m * ∏ k ∈ Icc 1 m, n / k

variable {c : ℕ}

lemma g_succ (n m : ℕ) : g c n (m + 1) = g c n m * (c * (n / (m + 1))) := by
  unfold g
  rw [Finset.prod_Icc_succ_top (by omega), pow_succ]
  ring

lemma g_mono (hc : 1 ≤ c) (n m : ℕ) : ∀ i, m + i ≤ n → g c n m ≤ g c n (m + i) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro h
    have h1 := ih (by omega)
    rw [← add_assoc, g_succ]
    have : 1 ≤ n / (m + i + 1) := (Nat.one_le_div_iff (by omega)).2 (by omega)
    have h2 : 1 * 1 ≤ c * (n / (m + i + 1)) := Nat.mul_le_mul hc this
    nlinarith

lemma g_pos (hc : 1 ≤ c) (n : ℕ) : 1 ≤ g c n n := by
  unfold g
  have : 0 < ∏ k ∈ Icc 1 n, n / k := by
    apply Finset.prod_pos
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact Nat.div_pos hk.2 (by omega)
  have : 0 < c ^ n := pow_pos (by omega) n
  nlinarith

lemma a_ge (n : ℕ) (hn : 1 ≤ n) : g c n n ≤ ag c n := by
  unfold ag
  have : g c n n ≤ ∑ m ∈ Icc 1 n, g c n m :=
    Finset.single_le_sum (f := g c n) (fun _ _ => Nat.zero_le _)
      (by simp [Finset.mem_Icc]; omega)
  unfold g at *
  omega

lemma a_le (hc : 1 ≤ c) (n : ℕ) : ag c n ≤ (n + 1) * g c n n := by
  unfold ag
  have h : ∑ m ∈ Icc 1 n, g c n m ≤ ∑ m ∈ Icc 1 n, g c n n := by
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have := g_mono hc n m (n - m) (by omega)
    rwa [show m + (n - m) = n by omega] at this
  simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h
  have hX := g_pos hc n
  unfold g at *
  have : n + 1 - 1 = n := by omega
  rw [this] at h
  nlinarith [h, hX]

/-- d j = log j - log (j - 1), with log 0 = 0. -/
def d (j : ℕ) : ℝ := Real.log j - Real.log ((j - 1 : ℕ) : ℝ)

lemma d_nonneg (j : ℕ) : 0 ≤ d j := by
  unfold d
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · have h1 : ((j - 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j 1
    rcases Nat.eq_zero_or_pos (j - 1) with h2 | h2
    · rw [h2]; simp; exact Real.log_natCast_nonneg j
    · have : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith [Real.log_le_log this h1]

lemma sum_d (m : ℕ) : ∑ j ∈ range (m + 1), d j = Real.log m := by
  induction m with
  | zero => simp [d]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp [d]

/-- log of the product of the floors as a sum over levels j. -/
lemma logP_eq (n : ℕ) :
    ∑ k ∈ Icc 1 n, Real.log ((n / k : ℕ) : ℝ) =
      ∑ j ∈ range (n + 1), d j * ((n / j : ℕ) : ℝ) := by
  have step : ∀ k ∈ Icc 1 n, Real.log ((n / k : ℕ) : ℝ) =
      ∑ j ∈ range (n + 1), if j ≤ n / k then d j else 0 := by
    intro k hk
    rw [← Finset.sum_filter]
    have : (range (n + 1)).filter (fun j => j ≤ n / k) = range (n / k + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have : n / k ≤ n := Nat.div_le_self n k
      omega
    rw [this, sum_d]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp [d]
  · have : (Icc 1 n).filter (fun k => j ≤ n / k) = Icc 1 (n / j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        refine ⟨h1, ?_⟩
        rw [Nat.le_div_iff_mul_le h1] at h3
        rw [Nat.le_div_iff_mul_le h]
        linarith
      · rintro ⟨h1, h2⟩
        rw [Nat.le_div_iff_mul_le h] at h2
        refine ⟨⟨h1, ?_⟩, ?_⟩
        · nlinarith
        · rw [Nat.le_div_iff_mul_le h1]; linarith
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
    ring

/-- The partial sums E n = ∑_{j ≤ n} d j / j. -/
def E (n : ℕ) : ℝ := ∑ j ∈ range (n + 1), d j / j

/-- The summand of log L. -/
def f (j : ℕ) : ℝ := Real.log j / (j * (j + 1))

lemma E_eq (N : ℕ) : E N = ∑ j ∈ range N, f j + Real.log N / N := by
  induction N with
  | zero => simp [E, d]
  | succ N ih =>
    unfold E at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [d, f, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hN : (0 : ℝ) < N := by exact_mod_cast h
      push_cast
      field_simp
      ring

lemma S_le (n : ℕ) :
    ∑ j ∈ range (n + 1), d j * ((n / j : ℕ) : ℝ) ≤ n * E n := by
  unfold E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h1 : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / j := Nat.cast_div_le
  have := d_nonneg j
  calc d j * ((n / j : ℕ) : ℝ) ≤ d j * ((n : ℝ) / j) :=
        mul_le_mul_of_nonneg_left h1 this
    _ = n * (d j / j) := by ring

lemma S_ge (n : ℕ) :
    n * E n - Real.log n ≤ ∑ j ∈ range (n + 1), d j * ((n / j : ℕ) : ℝ) := by
  unfold E
  rw [← sum_d n, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp [d]
  · have hj : (0 : ℝ) < j := by exact_mod_cast h
    have h1 : (n : ℝ) / j - 1 ≤ ((n / j : ℕ) : ℝ) := by
      have hdm := Nat.div_add_mod n j
      have hm := Nat.mod_lt n h
      rw [div_sub_one hj.ne', div_le_iff₀ hj]
      have : ((n % j : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast hm
      have : (n : ℝ) = j * ((n / j : ℕ) : ℝ) + ((n % j : ℕ) : ℝ) := by
        exact_mod_cast hdm.symm
      nlinarith
    have := d_nonneg j
    calc n * (d j / j) - d j = d j * ((n : ℝ) / j - 1) := by field_simp
      _ ≤ d j * ((n / j : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h1 this

lemma f_nonneg (j : ℕ) : 0 ≤ f j := by
  unfold f
  apply div_nonneg (Real.log_natCast_nonneg j)
  positivity

lemma f_summable : Summable f := by
  have hs : Summable (fun j : ℕ => 2 * ((j : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le f_nonneg (fun j => ?_) hs
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp [f]
  · have hj : (0 : ℝ) < j := by exact_mod_cast h
    have hsq : 0 < Real.sqrt j := Real.sqrt_pos.2 hj
    have hlog : Real.log j ≤ 2 * Real.sqrt j := by
      have := Real.log_le_sub_one_of_pos hsq
      rw [Real.log_sqrt hj.le] at this
      linarith
    have hpow : (j : ℝ) ^ ((3 : ℝ) / 2) = j * Real.sqrt j := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hj, Real.rpow_one,
        Real.sqrt_eq_rpow]
    unfold f
    rw [hpow]
    have hsj : Real.sqrt j * Real.sqrt j = j := Real.mul_self_sqrt hj.le
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [Real.log_natCast_nonneg j]

lemma log_div_tendsto :
    Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine this.congr (fun n => ?_)
  simp

lemma log_succ_div_tendsto :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp h1
  refine this.congr (fun n => ?_)
  simp

lemma E_tendsto : Tendsto E atTop (𝓝 (∑' j, f j)) := by
  have h1 : Tendsto (fun N => ∑ j ∈ range N, f j) atTop (𝓝 (∑' j, f j)) :=
    f_summable.hasSum.tendsto_sum_nat
  have := h1.add log_div_tendsto
  simp only [add_zero] at this
  exact this.congr (fun N => (E_eq N).symm)

/-- (1/n) log ∏_{k ≤ n} [n/k] tends to log L. -/
lemma S_tendsto :
    Tendsto (fun n : ℕ => (∑ j ∈ range (n + 1), d j * ((n / j : ℕ) : ℝ)) / n)
      atTop (𝓝 (∑' j, f j)) := by
  have lo : Tendsto (fun n : ℕ => E n - Real.log n / n) atTop (𝓝 (∑' j, f j)) := by
    simpa using E_tendsto.sub log_div_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lo E_tendsto ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    have := S_ge n
    have e : (E n - Real.log n / n) * n = n * E n - Real.log n := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have := S_le n
    linarith

lemma log_g (hc : 1 ≤ c) (n : ℕ) :
    Real.log (g c n n : ℝ) = n * Real.log c +
      ∑ j ∈ range (n + 1), d j * ((n / j : ℕ) : ℝ) := by
  rw [← logP_eq]
  unfold g
  push_cast
  have hpos : ∀ k ∈ Icc 1 n, ((n / k : ℕ) : ℝ) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have : 0 < n / k := Nat.div_pos hk.2 (by omega)
    exact_mod_cast this.ne'
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [Real.log_mul (pow_pos hc' n).ne' (Finset.prod_ne_zero_iff.2 hpos), Real.log_pow,
    Real.log_prod hpos]

/-- (1/n) log a(n) tends to log 2 + log L. -/
lemma loga_tendsto (hc : 1 ≤ c) :
    Tendsto (fun n : ℕ => Real.log (ag c n : ℝ) / n) atTop
      (𝓝 (Real.log c + ∑' j, f j)) := by
  set S := fun n : ℕ => (∑ j ∈ range (n + 1), d j * ((n / j : ℕ) : ℝ)) / n
  have lo : Tendsto (fun n => Real.log c + S n) atTop (𝓝 (Real.log c + ∑' j, f j)) :=
    S_tendsto.const_add _
  have hi : Tendsto (fun n => Real.log c + S n + Real.log ((n : ℝ) + 1) / n) atTop
      (𝓝 (Real.log c + ∑' j, f j)) := by
    simpa using lo.add log_succ_div_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hg : (1 : ℝ) ≤ g c n n := by exact_mod_cast g_pos hc n
    have ha : (g c n n : ℝ) ≤ ag c n := by exact_mod_cast a_ge n hn
    have := Real.log_le_log (by linarith) ha
    rw [log_g hc] at this
    simp only [S]
    rw [le_div_iff₀ hn']
    field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hg : (1 : ℝ) ≤ g c n n := by exact_mod_cast g_pos hc n
    have ha : (ag c n : ℝ) ≤ ((n : ℝ) + 1) * g c n n := by exact_mod_cast a_le hc n
    have ha0 : (0 : ℝ) < ag c n := by
      have := a_ge (c := c) n hn; have := g_pos hc n
      exact_mod_cast (show 0 < ag c n by omega)
    have := Real.log_le_log ha0 ha
    rw [Real.log_mul (by positivity) (by positivity), log_g hc] at this
    simp only [S]
    rw [div_le_iff₀ hn']
    field_simp
    linarith

/-- Base c: (ag c n)^(1/n) → c L. -/
theorem ag_limit (hc : 1 ≤ c) :
    Tendsto (fun n : ℕ => (ag c n : ℝ) ^ ((1 : ℝ) / n)) atTop
      (𝓝 (c * Real.exp (∑' j : ℕ, Real.log j / (j * (j + 1))))) := by
  have h := (Real.continuous_exp.tendsto _).comp (loga_tendsto hc)
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e : Real.exp (Real.log c + ∑' j, f j) =
      c * Real.exp (∑' j : ℕ, Real.log j / (j * (j + 1))) := by
    rw [Real.exp_add, Real.exp_log hc']
    rfl
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have ha0 : (0 : ℝ) < ag c n := by
    have := a_ge (c := c) n hn; have := g_pos hc n
    exact_mod_cast (show 0 < ag c n by omega)
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos ha0]
  ring_nf

/-- The conjecture of A208060: a(n)^(1/n) → 2L, log L = ∑_{j ≥ 1} log j / (j(j+1)). -/
theorem A208060_limit :
    Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) atTop
      (𝓝 (2 * Real.exp (∑' j : ℕ, Real.log j / (j * (j + 1))))) := by
  simpa [a_eq] using ag_limit (c := 2) (by norm_num)

/-- The conjecture of A075885: b(n)^(1/n) → L. -/
theorem A075885_limit :
    Tendsto (fun n : ℕ => (b n : ℝ) ^ ((1 : ℝ) / n)) atTop
      (𝓝 (Real.exp (∑' j : ℕ, Real.log j / (j * (j + 1))))) := by
  simpa [b_eq] using ag_limit (c := 1) le_rfl

end
