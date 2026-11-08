import Mathlib
import PNTPlus.Consequences

/-!
# PNTApps: densities from divergent sums of `1/p` over residue classes

Reusable statements for repo problems whose only analytic input is a prime-density fact.

Main results.
* `not_summable_one_div_prime_residue` : for a unit `a` of `ZMod q`, the sum of `1/p` over
  primes `p` with `(p : ZMod q) = a` diverges (from Mathlib's lower bound
  `LSeries_residueClass_lower_bound` for the L-series of `Λ` on a residue class, by a tail
  argument: `log p / p^x ≤ 1 / ((x - 1) p)`).
* `not_summable_one_div_prime_mod` : the same with `p % q = a % q` and `a` coprime to `q`.
* `count_mul_of_periodic`, `count_le_of_periodic`, `tendsto_count_div_of_periodic` : counting a
  predicate that depends only on `n % M`; its density is `count p M / M`.
* `count_and_of_coprime`, `count_forall_prod` : Chinese remainder counting, the number of
  `n < ∏ m_i` meeting conditions that depend on `n % m_i` (pairwise coprime) is the product.
* `density_zero_of_sieve` : let `P` be a set of primes with `∑_{p ∈ P} 1/p = ∞` and for each
  `p ∈ P` a property `G p n` depending only on `n % p^2` and true for at least `p - 1` residues
  mod `p^2`. Then the `n` with `G p n` false for every `p ∈ P` have natural density 0.
* `exists_prime_block` : for every `K` there is `X` with a prime in `(k m, (k + 1) m)` whenever
  `k < K` and `k m ≥ X` (the prime number theorem in short-interval form, from PNT+'s
  `prime_between`).
* `pi_le_div_log`, `sum_inv_primes_le` : `π(y) ≤ (2 log 4 + 2) y / log y` for `y ≥ 2` (from
  Mathlib's Chebyshev bound) and `∑_{p ≤ 2^J} 1/p ≤ (2 C₀ / log 2)(1 + log J)` (dyadic blocks).
* `IsSemiprime`, `semiprime_count_le`, `semiprime_count_bound` : the number of semiprimes up to
  `x` is at most `∑_{p ≤ √x} π(x/p)`, hence `≤ C x (1 + log (log₂ x + 1)) / log x` for `x ≥ 16`.
* `density_zero_or`, `tendsto_density_of_eq_off`, `tendsto_nth_div_of_density` : density zero
  is closed under union; changing a set on a density-zero set keeps its density; a set of
  density `d > 0` has `nth k / k → 1/d`.

Densities are stated with `Nat.count p N = #{n < N | p n}`.

Checked: everything above, axioms propext, Classical.choice, Quot.sound. New code; the analytic
inputs are Mathlib's Dirichlet L-series bound and the vendored PNT+ (`prime_between`).
-/

namespace OpenProblemsLib.PNTApps

open Filter Topology Finset

/-! ## Divergence of `∑ 1/p` over a residue class -/

open ArithmeticFunction vonMangoldt in
/-- Dirichlet: `∑ 1/p` over primes `p` with `(p : ZMod q) = a` diverges, `a` a unit. -/
theorem not_summable_one_div_prime_residue {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0) := by
  intro hS
  set f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]; split_ifs <;> positivity
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have hA := summable_residueClass_non_primes_div a
  set A := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n
  set φ : ℝ := (q.totient : ℝ)⁻¹
  have hφ : 0 < φ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  have htail : Tendsto (fun N => ∑' k, f (k + N)) atTop (𝓝 0) := tendsto_sum_nat_add f
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds (half_pos hφ))).exists
  set T := ∑' k, f (k + N)
  have hT0 : 0 ≤ T := tsum_nonneg fun k => hf0 _
  set B := ∑ n ∈ range N, residueClass a n / n
  -- The tail of `f` beyond `N` as a function on `ℕ`.
  set g : ℕ → ℝ := fun n => if N ≤ n then f n else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> simp [hf0]
  have hgS : Summable g := Summable.of_nonneg_of_le hg0
    (fun n => by simp only [hg]; split_ifs <;> simp [hf0]) hS
  have hgT : ∑' n, g n = T := by
    rw [← hgS.sum_add_tsum_nat_add N]
    have h1 : ∑ i ∈ range N, g i = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hg, Finset.mem_range.mp hi]
    rw [h1, zero_add]
    exact tsum_congr fun k => by simp [hg]
  -- Upper bound of the L-series for `x ∈ (1, 2]`.
  have key : ∀ x : ℝ, x ∈ Set.Ioc 1 2 →
      ∑' n : ℕ, residueClass a n / (n : ℝ) ^ x ≤ A + B + T / (x - 1) := by
    intro x hx
    have hx1 : 0 < x - 1 := sub_pos.mpr hx.1
    set h : ℕ → ℝ := fun n => (if n.Prime then 0 else residueClass a n) / n +
      (if n < N then residueClass a n / n else 0) + g n / (x - 1) with hh
    have hfin : Summable (fun n : ℕ => if n < N then residueClass a n / n else 0) :=
      summable_of_ne_finset_zero (s := range N) fun n hn => by
        simp [Finset.mem_range.not.mp hn]
    have hfinsum : ∑' n : ℕ, (if n < N then residueClass a n / n else 0) = B := by
      rw [tsum_eq_sum (s := range N) fun n hn => by simp [Finset.mem_range.not.mp hn]]
      exact Finset.sum_congr rfl fun n hn => by simp [Finset.mem_range.mp hn]
    have hhS : Summable h := (hA.add hfin).add (hgS.div_const _)
    have hhsum : ∑' n, h n = A + B + T / (x - 1) := by
      rw [show h = fun n => ((if n.Prime then 0 else residueClass a n) / n +
          (if n < N then residueClass a n / n else 0)) + g n / (x - 1) from rfl,
        (hA.add hfin).tsum_add (hgS.div_const _), hA.tsum_add hfin, hfinsum,
        tsum_div_const, hgT]
    have hLS : Summable (fun n : ℕ => residueClass a n / (n : ℝ) ^ x) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx.1
    refine (Summable.tsum_le_tsum (fun n => ?_) hLS hhS).trans hhsum.le
    have hr0 := residueClass_nonneg a n
    have e1 : 0 ≤ (if n.Prime then 0 else residueClass a n) / n := by
      split_ifs <;> positivity
    have e2 : 0 ≤ (if n < N then residueClass a n / n else 0) := by
      split_ifs <;> positivity
    have e3 : 0 ≤ g n / (x - 1) := div_nonneg (hg0 n) hx1.le
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [residueClass_apply_zero, zero_div]
      exact add_nonneg (add_nonneg e1 e2) e3
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ x := by
      conv_lhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hnR hx.1.le
    have hle1 : residueClass a n / (n : ℝ) ^ x ≤ residueClass a n / n :=
      div_le_div_of_nonneg_left hr0 (by positivity) hpow
    simp only [hh]
    by_cases hp : n.Prime
    · by_cases hnN : n < N
      · simp only [hnN, ↓reduceIte]; linarith
      · -- `n ≥ N` prime.
        by_cases hmod : (n : ZMod q) = a
        · have hres : residueClass a n = Real.log n := by
            simp [residueClass, Set.indicator, hmod, vonMangoldt_apply_prime hp]
          have hgn : g n = 1 / n := by simp [hg, hf, hp, hmod, not_lt.mp hnN]
          rw [hres, hgn]
          have hlog : Real.log n ≤ (n : ℝ) ^ (x - 1) / (x - 1) :=
            Real.log_le_rpow_div (by positivity) hx1
          have hsplit : (n : ℝ) ^ x = n * (n : ℝ) ^ (x - 1) := by
            rw [← Real.rpow_one_add' (by positivity) (by linarith)]
            congr 1; ring
          have hpos : 0 < (n : ℝ) ^ (x - 1) := by positivity
          have : Real.log n / (n : ℝ) ^ x ≤ 1 / n / (x - 1) := by
            rw [hsplit, div_le_iff₀ (by positivity)]
            calc Real.log n ≤ (n : ℝ) ^ (x - 1) / (x - 1) := hlog
              _ = 1 / n / (x - 1) * (n * (n : ℝ) ^ (x - 1)) := by
                field_simp
          simp only [hnN, ↓reduceIte] at e2 ⊢
          simp only [hp, ↓reduceIte] at e1 ⊢
          linarith
        · have hres : residueClass a n = 0 := by
            simp [residueClass, Set.indicator, hmod]
          have h0 : residueClass a n / (n : ℝ) ^ x = 0 := by rw [hres, zero_div]
          rw [h0]; exact add_nonneg (add_nonneg e1 e2) e3
    · simp only [hp, ↓reduceIte]; linarith
  -- Combine with the lower bound at `x = 1 + ε`.
  set D := A + B + C'
  set ε := min 1 (φ / (4 * (|D| + 1)))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ φ / (4 * (|D| + 1)) := min_le_right _ _
  have hx : 1 + ε ∈ Set.Ioc 1 2 := ⟨by linarith, by linarith⟩
  have h1 := (hC' hx).trans (key _ hx)
  rw [show 1 + ε - 1 = ε by ring] at h1
  have h2 : φ - T ≤ D * ε := by
    have := mul_le_mul_of_nonneg_right h1 hε.le
    rw [sub_mul, add_mul, div_mul_cancel₀ _ hε.ne', div_mul_cancel₀ _ hε.ne'] at this
    simp only [D]; nlinarith
  have h3 : D * ε ≤ |D| * (φ / (4 * (|D| + 1))) :=
    (mul_le_mul_of_nonneg_right (le_abs_self D) hε.le).trans
      (mul_le_mul_of_nonneg_left hε2 (abs_nonneg D))
  have h4 : |D| * (φ / (4 * (|D| + 1))) ≤ φ / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg D]
  linarith

/-- Dirichlet: `∑ 1/p` over primes `p ≡ a (mod q)` diverges when `a` is coprime to `q > 0`. -/
theorem not_summable_one_div_prime_mod {q a : ℕ} (hq : 0 < q) (h : a.Coprime q) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ n % q = a % q then (1 : ℝ) / n else 0) := by
  have : NeZero q := ⟨hq.ne'⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr h
  convert not_summable_one_div_prime_residue hu using 3 with n
  simp only [ZMod.natCast_eq_natCast_iff']

/-! ## Periodic counting -/

/-- A predicate depending only on `n % M` has `count p (M k) = k · count p M`. -/
theorem count_mul_of_periodic (p : ℕ → Prop) [DecidablePred p] {M : ℕ}
    (hp : ∀ n, p n ↔ p (n % M)) (k : ℕ) : Nat.count p (M * k) = k * Nat.count p M := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    refine Finset.filter_congr fun j _ => ?_
    rw [hp (M * k + j), hp j, Nat.mul_add_mod]

theorem count_le_of_periodic (p : ℕ → Prop) [DecidablePred p] {M : ℕ} (hM : 0 < M)
    (hp : ∀ n, p n ↔ p (n % M)) (N : ℕ) : Nat.count p N ≤ (N / M + 1) * Nat.count p M := by
  rw [← count_mul_of_periodic p hp]
  exact Nat.count_monotone p (Nat.lt_mul_div_succ N hM).le

theorem le_count_of_periodic (p : ℕ → Prop) [DecidablePred p] {M : ℕ}
    (hp : ∀ n, p n ↔ p (n % M)) (N : ℕ) : N / M * Nat.count p M ≤ Nat.count p N := by
  rw [← count_mul_of_periodic p hp]
  exact Nat.count_monotone p (Nat.mul_div_le N M)

/-- A predicate depending only on `n % M` has density `count p M / M`. -/
theorem tendsto_count_div_of_periodic (p : ℕ → Prop) [DecidablePred p] {M : ℕ} (hM : 0 < M)
    (hp : ∀ n, p n ↔ p (n % M)) :
    Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop
      (𝓝 ((Nat.count p M : ℝ) / M)) := by
  set c : ℝ := (Nat.count p M : ℝ)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hlim : ∀ s : ℝ, Tendsto (fun N : ℕ => c / M + s * (c / N)) atTop (𝓝 (c / M)) := by
    intro s
    have := (tendsto_const_div_atTop_nhds_zero_nat c).const_mul s
    simpa using (tendsto_const_nhds (x := c / M)).add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-1)) (hlim 1) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 := le_count_of_periodic p hp N
    have h2 : (N : ℝ) < M * ((N / M : ℕ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ N hM
    have h3 : ((N / M : ℕ) : ℝ) * c ≤ Nat.count p N := by simp only [c]; exact_mod_cast h1
    rw [le_div_iff₀ hNR]
    have hc : 0 ≤ c := by positivity
    have hq : (N : ℝ) / M - 1 ≤ ((N / M : ℕ) : ℝ) := by
      rw [div_sub_one hMR.ne', div_le_iff₀ hMR]; linarith
    have : c / M * N - c ≤ ((N / M : ℕ) : ℝ) * c := by
      have := mul_le_mul_of_nonneg_left hq hc
      have e2 : c * ((N : ℝ) / M - 1) = c / M * N - c := by ring
      linarith
    have e : (c / M + -1 * (c / N)) * N = c / M * N - c := by
      rw [add_mul, neg_one_mul, neg_mul, div_mul_cancel₀ c hNR.ne', sub_eq_add_neg]
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 := count_le_of_periodic p hM hp N
    have h2 : ((N / M : ℕ) : ℝ) * M ≤ N := by exact_mod_cast Nat.div_mul_le_self N M
    have h3 : (Nat.count p N : ℝ) ≤ (((N / M : ℕ) : ℝ) + 1) * c := by
      simp only [c]; exact_mod_cast h1
    rw [div_le_iff₀ hNR]
    have hc : 0 ≤ c := by positivity
    have hq : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := Nat.cast_div_le
    have : ((N / M : ℕ) : ℝ) * c ≤ c / M * N := by
      have := mul_le_mul_of_nonneg_right hq hc
      have e2 : (N : ℝ) / M * c = c / M * N := by ring
      linarith
    have e : (c / M + 1 * (c / N)) * N = c / M * N + c := by
      rw [add_mul, one_mul, div_mul_cancel₀ c hNR.ne']
    linarith

/-- Exactly `m` of the `n < q m` are multiples of `q`. -/
theorem count_dvd_mul {q : ℕ} (hq : 0 < q) (m : ℕ) : Nat.count (fun n => q ∣ n) (q * m) = m := by
  rw [count_mul_of_periodic _ (fun n => (Nat.dvd_mod_iff dvd_rfl).symm) m]
  have h1 : Nat.count (fun n => q ∣ n) q = 1 := by
    rw [Nat.count_eq_card_filter_range]
    have : (range q).filter (fun n => q ∣ n) = {0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; exact Nat.eq_zero_of_dvd_of_lt h2 h1
      · rintro rfl; exact ⟨hq, dvd_zero q⟩
    rw [this, Finset.card_singleton]
  rw [h1, mul_one]

/-- Exactly `m (q - 1)` of the `n < q m` are not multiples of `q`. -/
theorem count_not_dvd_mul {q : ℕ} (hq : 0 < q) (m : ℕ) :
    Nat.count (fun n => ¬ q ∣ n) (q * m) = m * (q - 1) := by
  have h := count_dvd_mul hq m
  have hsum : Nat.count (fun n => q ∣ n) (q * m) + Nat.count (fun n => ¬ q ∣ n) (q * m) =
      q * m := by
    simp only [Nat.count_eq_card_filter_range]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  rw [h] at hsum
  rw [Nat.mul_sub, mul_one, mul_comm m q]
  omega

/-! ## Chinese remainder counting -/

theorem count_and_of_coprime (p r : ℕ → Prop) [DecidablePred p] [DecidablePred r] {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (co : a.Coprime b) (hp : ∀ n, p n ↔ p (n % a))
    (hr : ∀ n, r n ↔ r (n % b)) :
    Nat.count (fun n => p n ∧ r n) (a * b) = Nat.count p a * Nat.count r b := by
  simp only [Nat.count_eq_card_filter_range]
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun n => (n % a, n % b))
    (fun x => (Nat.chineseRemainder co x.1 x.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, Set.mem_prod,
      Set.mem_ofPred_eq]
    exact ⟨⟨Nat.mod_lt _ ha, (hp n).mp hn.2.1⟩, ⟨Nat.mod_lt _ hb, (hr n).mp hn.2.2⟩⟩
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, Set.mem_prod,
      Set.mem_ofPred_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    have c1 := (Nat.chineseRemainder co x.1 x.2).2.1
    have c2 := (Nat.chineseRemainder co x.1 x.2).2.2
    refine ⟨Nat.chineseRemainder_lt_mul co _ _ ha.ne' hb.ne', ?_, ?_⟩
    · rw [hp, c1, Nat.mod_eq_of_lt hx.1.1]; exact hx.1.2
    · rw [hr, c2, Nat.mod_eq_of_lt hx.2.1]; exact hx.2.2
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    have hu := Nat.chineseRemainder_modEq_unique co (Nat.mod_modEq n a).symm
      (Nat.mod_modEq n b).symm
    have hlt := Nat.chineseRemainder_lt_mul co (n % a) (n % b) ha.ne' hb.ne'
    unfold Nat.ModEq at hu
    rw [Nat.mod_eq_of_lt hn.1, Nat.mod_eq_of_lt hlt] at hu
    exact hu.symm
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, Set.mem_prod,
      Set.mem_ofPred_eq] at hx
    have c1 := (Nat.chineseRemainder co x.1 x.2).2.1
    have c2 := (Nat.chineseRemainder co x.1 x.2).2.2
    unfold Nat.ModEq at c1 c2
    ext
    · simp only; rw [c1, Nat.mod_eq_of_lt hx.1.1]
    · simp only; rw [c2, Nat.mod_eq_of_lt hx.2.1]

open Classical in
/-- Conditions `Q i` depending on `n % m i` (pairwise coprime `m i`) are met by exactly
`∏ count (Q i) (m i)` of the `n < ∏ m i`. -/
theorem count_forall_prod (T : Finset ℕ) (m : ℕ → ℕ) (hm : ∀ i ∈ T, 0 < m i)
    (hco : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (m i).Coprime (m j)) (Q : ℕ → ℕ → Prop)
    (hQ : ∀ i ∈ T, ∀ n, Q i n ↔ Q i (n % m i)) :
    Nat.count (fun n => ∀ i ∈ T, Q i n) (∏ i ∈ T, m i) = ∏ i ∈ T, Nat.count (Q i) (m i) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
    simp
  | insert j T hj ih =>
    have hmT : ∀ i ∈ T, 0 < m i := fun i hi => hm i (Finset.mem_insert_of_mem hi)
    have ih' := ih hmT (fun i hi k hk => hco i (Finset.mem_insert_of_mem hi) k
      (Finset.mem_insert_of_mem hk)) (fun i hi => hQ i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ← ih']
    have hcop : (m j).Coprime (∏ i ∈ T, m i) := Nat.Coprime.prod_right fun i hi =>
      hco j (Finset.mem_insert_self j T) i (Finset.mem_insert_of_mem hi)
        (fun h => hj (h ▸ hi))
    have hP : 0 < ∏ i ∈ T, m i := Finset.prod_pos hmT
    have := count_and_of_coprime (Q j) (fun n => ∀ i ∈ T, Q i n) (hm j (Finset.mem_insert_self j T))
      hP hcop (hQ j (Finset.mem_insert_self j T)) (fun n => by
        constructor
        · intro h i hi
          rw [hQ i (Finset.mem_insert_of_mem hi), Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem m hi),
            ← hQ i (Finset.mem_insert_of_mem hi)]
          exact h i hi
        · intro h i hi
          have := h i hi
          rw [hQ i (Finset.mem_insert_of_mem hi), Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem m hi),
            ← hQ i (Finset.mem_insert_of_mem hi)] at this
          exact this)
    convert this using 2
    · funext n
      simp only [Finset.mem_insert, forall_eq_or_imp]

/-! ## The sieve: density zero from a divergent `∑ 1/p` -/

open Classical in
/-- Let `P` be primes with `∑_{p ∈ P} 1/p = ∞`, and for `p ∈ P` let `G p n` depend only on
`n % p^2` and hold for at least `p - 1` residues mod `p^2`. Then the `n` for which every `G p n`
fails have density 0. -/
theorem density_zero_of_sieve (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdiv : ¬ Summable (fun n : ℕ => if n ∈ P then (1 : ℝ) / n else 0))
    (G : ℕ → ℕ → Prop) (hper : ∀ p ∈ P, ∀ n, G p n ↔ G p (n % p ^ 2))
    (hcnt : ∀ p ∈ P, p - 1 ≤ Nat.count (G p) (p ^ 2)) :
    Tendsto (fun N : ℕ => (Nat.count (fun n => ∀ p ∈ P, ¬ G p n) N : ℝ) / N) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun n => if n ∈ P then (1 : ℝ) / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; split_ifs <;> positivity
  have hpart := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp hdiv
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := (hpart.eventually (eventually_ge_atTop (2 * Real.log (2 / ε)))).exists
  set T := (range K).filter (· ∈ P)
  have hTP : ∀ p ∈ T, p ∈ P := fun p hp => (Finset.mem_filter.mp hp).2
  set c : ℕ → ℕ := fun p => Nat.count (fun n => ¬ G p n) (p ^ 2)
  set M := ∏ p ∈ T, p ^ 2
  have hMpos : 0 < M := Finset.prod_pos fun p hp => pow_pos (hP p (hTP p hp)).pos 2
  -- Counting `n < M` with every `G p n` false, `p ∈ T`.
  have hcountM : Nat.count (fun n => ∀ p ∈ T, ¬ G p n) M = ∏ p ∈ T, c p := by
    convert count_forall_prod T (fun p => p ^ 2) (fun p hp => pow_pos (hP p (hTP p hp)).pos 2)
      (fun i hi j hj hij => Nat.Coprime.pow 2 2
        ((Nat.coprime_primes (hP i (hTP i hi)) (hP j (hTP j hj))).mpr hij))
      (fun p n => ¬ G p n) (fun p hp n => not_congr (hper p (hTP p hp) n))
  have hperT : ∀ n, (∀ p ∈ T, ¬ G p n) ↔ (∀ p ∈ T, ¬ G p (n % M)) := by
    intro n
    refine forall₂_congr fun p hp => not_congr ?_
    rw [hper p (hTP p hp) n, hper p (hTP p hp) (n % M),
      Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem (fun p => p ^ 2) hp)]
  -- Each local factor is at most `1 - 1/(2p)` of `p^2`.
  have hloc : ∀ p ∈ T, (c p : ℝ) / (p ^ 2 : ℕ) ≤ Real.exp (-(1 / (2 * (p : ℝ)))) := by
    intro p hp
    have hpp := hP p (hTP p hp)
    have h2 := hpp.two_le
    have hsum : c p + Nat.count (G p) (p ^ 2) = p ^ 2 := by
      simp only [c, Nat.count_eq_card_filter_range]
      rw [add_comm, Finset.card_filter_add_card_filter_not, Finset.card_range]
    have hcN : c p + (p - 1) ≤ p ^ 2 := by have := hcnt p (hTP p hp); omega
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hcR : (c p : ℝ) + ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by
      have : ((c p + (p - 1) : ℕ) : ℝ) ≤ ((p ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcN
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at this; linarith
    have hstep : (c p : ℝ) / (p ^ 2 : ℕ) ≤ 1 + (-(1 / (2 * (p : ℝ)))) := by
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have : (1 + -(1 / (2 * (p : ℝ)))) * (p : ℝ) ^ 2 = (p : ℝ) ^ 2 - p / 2 := by
        field_simp; ring
      rw [this]; linarith
    exact hstep.trans (by linarith [Real.add_one_le_exp (-(1 / (2 * (p : ℝ))))])
  have hprod : (∏ p ∈ T, (c p : ℝ)) / M ≤ ε / 2 := by
    have e1 : (∏ p ∈ T, (c p : ℝ)) / M = ∏ p ∈ T, ((c p : ℝ) / (p ^ 2 : ℕ)) := by
      simp only [M]; push_cast; rw [Finset.prod_div_distrib]
    rw [e1]
    calc ∏ p ∈ T, ((c p : ℝ) / (p ^ 2 : ℕ))
        ≤ ∏ p ∈ T, Real.exp (-(1 / (2 * (p : ℝ)))) :=
          Finset.prod_le_prod₀ (fun p _ => by positivity) hloc
      _ = Real.exp (-(∑ i ∈ range K, f i) / 2) := by
          rw [← Real.exp_sum]; congr 1
          rw [Finset.sum_filter, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hf]; split_ifs <;> ring
      _ ≤ Real.exp (-(Real.log (2 / ε))) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = ε / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  -- Choose `N₀` with `∏ c p / N₀ < ε / 2`.
  set Cc : ℝ := ∏ p ∈ T, (c p : ℝ)
  have hCc : 0 ≤ Cc := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * Cc / ε)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hN1 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNbig : 2 * Cc / ε < N := by
    have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  have hmono : Nat.count (fun n => ∀ p ∈ P, ¬ G p n) N ≤
      Nat.count (fun n => ∀ p ∈ T, ¬ G p n) N :=
    Nat.count_mono_left fun k _ hk p hp => hk p (hTP p hp)
  have hle := count_le_of_periodic _ hMpos hperT N
  rw [hcountM] at hle
  have hle' : (Nat.count (fun n => ∀ p ∈ P, ¬ G p n) N : ℝ) ≤ ((N / M : ℕ) + 1 : ℝ) * Cc := by
    have := hmono.trans hle
    simp only [Cc]; exact_mod_cast this
  have hdivle : ((N / M : ℕ) : ℝ) ≤ N / M := Nat.cast_div_le
  have hval0 : 0 ≤ (Nat.count (fun n => ∀ p ∈ P, ¬ G p n) N : ℝ) / N := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hval0, div_lt_iff₀ hN1]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have h1 : ((N / M : ℕ) : ℝ) * Cc ≤ N * (Cc / M) := by
    calc ((N / M : ℕ) : ℝ) * Cc ≤ (N / M) * Cc := mul_le_mul_of_nonneg_right hdivle hCc
      _ = N * (Cc / M) := by ring
  have h2 : N * (Cc / M) ≤ N * (ε / 2) := mul_le_mul_of_nonneg_left hprod hN1.le
  have h3 : Cc < ε / 2 * N := by
    rw [div_lt_iff₀ hε] at hNbig; linarith
  nlinarith

/-! ## Primes in short intervals (prime number theorem) -/

/-- For every `K` there is `X` such that `(k m, (k + 1) m)` contains a prime whenever `k < K`
and `k m ≥ X`: from `prime_between` (PNT+) with `ε = 1 / K`. -/
theorem exists_prime_block (K : ℕ) : ∃ X : ℕ, ∀ k m : ℕ, k < K → X ≤ k * m →
    ∃ p : ℕ, p.Prime ∧ k * m < p ∧ p < (k + 1) * m := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨0, fun k m hk _ => absurd hk (Nat.not_lt_zero _)⟩
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (prime_between (ε := 1 / (K : ℝ)) (by positivity))
  refine ⟨⌈a⌉₊ + 1, fun k m hk hX => ?_⟩
  have hkm : (a : ℝ) ≤ (k * m : ℕ) := by
    have h1 : (a : ℝ) ≤ ⌈a⌉₊ := Nat.le_ceil a
    have h2 : ((⌈a⌉₊ + 1 : ℕ) : ℝ) ≤ (k * m : ℕ) := by exact_mod_cast hX
    push_cast at h2 ⊢; linarith
  obtain ⟨p, hp, h1, h2⟩ := ha _ hkm
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hX
    · exact h
  refine ⟨p, hp, by exact_mod_cast h1, ?_⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkK : (k : ℝ) < K := by exact_mod_cast hk
  have : (1 + 1 / (K : ℝ)) * ((k * m : ℕ) : ℝ) ≤ ((k + 1) * m : ℕ) := by
    push_cast
    have e : (1 + 1 / (K : ℝ)) * (k * m) = k * m + (k / K) * m := by field_simp
    rw [e]
    have : (k : ℝ) / K ≤ 1 := (div_le_one hKR).mpr hkK.le
    nlinarith
  exact_mod_cast h2.trans_le this

/-! ## Chebyshev, dyadic Mertens and semiprime counts -/

section Semiprimes
open Real

/-- Chebyshev: `π(y) ≤ C₀ y / log y` for natural `y ≥ 2`, `C₀ = 2 log 4 + 2`. -/
theorem pi_le_div_log (y : ℕ) (hy : 2 ≤ y) :
    (Nat.primeCounting y : ℝ) ≤ (2 * log 4 + 2) * y / log y := by
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have h := Chebyshev.pi_le_log4_mul_div (x := (y : ℝ)) (by linarith)
  rw [Nat.floor_natCast, log_sqrt (by positivity)] at h
  have hlog : 0 < log (y : ℝ) := log_pos (by linarith)
  have hs : √(y : ℝ) ≤ 2 * y / log y := by
    have h1 : log (y : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      log_le_rpow_div (by positivity) (by norm_num)
    rw [← sqrt_eq_rpow] at h1
    rw [le_div_iff₀ hlog]
    have hsq : √(y : ℝ) * √(y : ℝ) = y := mul_self_sqrt (by positivity)
    have : 0 ≤ √(y : ℝ) := sqrt_nonneg _
    nlinarith
  calc (Nat.primeCounting y : ℝ) ≤ log 4 * y / (log y / 2) + √(y : ℝ) := h
    _ ≤ log 4 * y / (log y / 2) + 2 * y / log y := by linarith
    _ = (2 * log 4 + 2) * y / log y := by field_simp

theorem primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = ((range (n + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- Dyadic Mertens bound: `∑_{p ≤ 2^J} 1/p ≤ (2 C₀ / log 2) (1 + log J)`. -/
theorem sum_inv_primes_le (J : ℕ) :
    ∑ p ∈ (range (2 ^ J + 1)).filter Nat.Prime, (1 : ℝ) / p ≤
      2 * (2 * log 4 + 2) / log 2 * (1 + log J) := by
  set C₀ : ℝ := 2 * log 4 + 2
  have hC₀ : 0 < C₀ := by positivity
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  set S := (range (2 ^ J + 1)).filter Nat.Prime
  have hmaps : ∀ p ∈ S, Nat.log 2 (p - 1) ∈ range J := by
    intro p hp
    simp only [S, mem_filter, mem_range] at hp
    have h2 := hp.2.two_le
    rw [mem_range]
    exact Nat.log_lt_of_lt_pow (by omega) (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range J, ∑ p ∈ S with Nat.log 2 (p - 1) = j, (1 : ℝ) / p ≤
      2 * C₀ / log 2 * (1 / ((j : ℝ) + 1)) := by
    intro j _
    set F := S.filter (fun p => Nat.log 2 (p - 1) = j)
    have hmem : ∀ p ∈ F, p.Prime ∧ 2 ^ j < p ∧ p ≤ 2 ^ (j + 1) := by
      intro p hp
      simp only [F, S, mem_filter, mem_range] at hp
      obtain ⟨⟨_, hpr⟩, hlog⟩ := hp
      have h2 := hpr.two_le
      have a1 : 2 ^ Nat.log 2 (p - 1) ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
      have a2 : p - 1 < 2 ^ (Nat.log 2 (p - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      rw [hlog] at a1 a2
      exact ⟨hpr, by omega, by omega⟩
    have hcard : (F.card : ℝ) ≤ Nat.primeCounting (2 ^ (j + 1)) := by
      rw [primeCounting_eq_card]
      exact_mod_cast card_le_card fun p hp => by
        obtain ⟨hpr, _, h3⟩ := hmem p hp
        simp only [mem_filter, mem_range]; exact ⟨by omega, hpr⟩
    have hpi := pi_le_div_log (2 ^ (j + 1)) (by
      have : 2 ^ 1 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this)
    have hterm : ∀ p ∈ F, (1 : ℝ) / p ≤ 1 / 2 ^ j := by
      intro p hp
      obtain ⟨_, h1, _⟩ := hmem p hp
      have : (2 : ℝ) ^ j ≤ p := by exact_mod_cast h1.le
      exact one_div_le_one_div_of_le (by positivity) this
    calc ∑ p ∈ F, (1 : ℝ) / p ≤ ∑ p ∈ F, (1 : ℝ) / 2 ^ j := sum_le_sum hterm
      _ = F.card * (1 / 2 ^ j) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ Nat.primeCounting (2 ^ (j + 1)) * (1 / 2 ^ j) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ C₀ * ((2 ^ (j + 1) : ℕ) : ℝ) / log ((2 ^ (j + 1) : ℕ) : ℝ) * (1 / 2 ^ j) :=
          mul_le_mul_of_nonneg_right hpi (by positivity)
      _ = 2 * C₀ / log 2 * (1 / ((j : ℝ) + 1)) := by
          push_cast
          rw [Real.log_pow]
          push_cast
          field_simp
          ring
  calc ∑ j ∈ range J, ∑ p ∈ S with Nat.log 2 (p - 1) = j, (1 : ℝ) / p
      ≤ ∑ j ∈ range J, 2 * C₀ / log 2 * (1 / ((j : ℝ) + 1)) := sum_le_sum hfib
    _ = 2 * C₀ / log 2 * (harmonic J : ℝ) := by
        rw [← mul_sum]; congr 1
        simp [harmonic]
    _ ≤ 2 * C₀ / log 2 * (1 + log J) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J) (by positivity)

/-- `m` is a semiprime: exactly two prime factors with multiplicity. -/
def IsSemiprime (m : ℕ) : Prop := m.primeFactorsList.length = 2

instance : DecidablePred IsSemiprime := fun m => by unfold IsSemiprime; infer_instance

theorem semiprime_structure {m : ℕ} (hm : IsSemiprime m) :
    m.minFac.Prime ∧ (m / m.minFac).Prime ∧ m.minFac ≤ m / m.minFac ∧
      m = m.minFac * (m / m.minFac) := by
  unfold IsSemiprime at hm
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · simp at hm
    · simp at hm
    · omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [Nat.primeFactorsList_add_two] at hm
  simp only [List.length_cons] at hm
  set q := (n + 2) / (n + 2).minFac
  have hl : q.primeFactorsList.length = 1 := by omega
  obtain ⟨r, hr⟩ : ∃ r, q.primeFactorsList = [r] := List.length_eq_one_iff.mp hl
  have hq0 : q ≠ 0 := by intro h; rw [h] at hr; simp at hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hr]; simp)
  have hqr : q = r := by
    have := Nat.prod_primeFactorsList hq0; rw [hr] at this; simpa using this.symm
  have hqp : q.Prime := hqr ▸ hrp
  have hmp : (n + 2).minFac.Prime := Nat.minFac_prime (by omega)
  have hdecomp : n + 2 = (n + 2).minFac * q := (Nat.mul_div_cancel' (Nat.minFac_dvd _)).symm
  refine ⟨hmp, hqp, Nat.minFac_le_of_dvd hqp.two_le ⟨(n + 2).minFac, by rw [mul_comm]; exact hdecomp⟩,
    hdecomp⟩

/-- Semiprimes up to `x`: at most `∑_{p ≤ √x} π(x / p)`. -/
theorem semiprime_count_le (x : ℕ) :
    ((range (x + 1)).filter IsSemiprime).card ≤
      ∑ p ∈ (range (Nat.sqrt x + 1)).filter Nat.Prime, Nat.primeCounting (x / p) := by
  set P := (range (Nat.sqrt x + 1)).filter Nat.Prime
  set T := P.biUnion (fun p => ((range (x / p + 1)).filter Nat.Prime).image (fun q => (p, q)))
  have h1 : ((range (x + 1)).filter IsSemiprime).card ≤ T.card := by
    refine card_le_card_of_injOn (fun m => (m.minFac, m / m.minFac)) ?_ ?_
    · intro m hm
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hm
      obtain ⟨hp, hq, hpq, hdec⟩ := semiprime_structure hm.2
      have hpos := hp.pos
      simp only [T, P, coe_biUnion, coe_filter, mem_range, Set.mem_ofPred_eq, Set.mem_iUnion,
        coe_image, Set.mem_image, exists_prop]
      refine ⟨m.minFac, ⟨?_, hp⟩, m / m.minFac, ⟨?_, hq⟩, rfl⟩
      · have : m.minFac * m.minFac ≤ x := by
          calc m.minFac * m.minFac ≤ m.minFac * (m / m.minFac) := Nat.mul_le_mul_left _ hpq
            _ = m := hdec.symm
            _ ≤ x := by omega
        have := Nat.le_sqrt.mpr this
        omega
      · have : m / m.minFac ≤ x / m.minFac := Nat.div_le_div_right (by omega)
        omega
    · intro m hm m' hm' h
      simp only [Prod.mk.injEq] at h
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hm hm'
      exact (semiprime_structure hm.2).2.2.2.trans
        ((congrArg₂ (· * ·) h.1 h.2).trans (semiprime_structure hm'.2).2.2.2.symm)
  have h2 : T.card ≤ ∑ p ∈ P, Nat.primeCounting (x / p) := by
    refine (card_biUnion_le).trans (sum_le_sum fun p _ => ?_)
    rw [primeCounting_eq_card]
    exact card_image_le
  exact h1.trans h2

/-- `S(x) ≤ C x (1 + log J) / log x` with `J = log₂ x + 1`, for `x ≥ 16`. -/
theorem semiprime_count_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 16 ≤ x →
    (((range (x + 1)).filter IsSemiprime).card : ℝ) ≤
      C * x * (1 + log ((Nat.log 2 x + 1 : ℕ) : ℝ)) / log x := by
  set C₀ : ℝ := 2 * log 4 + 2
  have hC₀ : 0 < C₀ := by positivity
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨4 * C₀ * (2 * C₀ / log 2), by positivity, fun x hx => ?_⟩
  set J := Nat.log 2 x + 1
  set s := Nat.sqrt x
  have hs4 : 4 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hxR : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx : 0 < log (x : ℝ) := log_pos (by linarith)
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs4
  -- `log x ≤ 4 log s`.
  have hxs : log (x : ℝ) ≤ 4 * log s := by
    have h1 : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
    have h2 : (x : ℝ) ≤ 4 * s ^ 2 := by
      have : x ≤ 4 * s ^ 2 := by nlinarith
      exact_mod_cast this
    have h3 : log (x : ℝ) ≤ log (4 * (s : ℝ) ^ 2) := log_le_log (by linarith) h2
    rw [log_mul (by norm_num) (by positivity), log_pow] at h3
    have h4 : log (4 : ℝ) ≤ log (s : ℝ) * 2 := by
      have h5 : (4 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
      have h6 := log_le_log (by norm_num) h5
      rw [log_pow] at h6; push_cast at h6; linarith
    push_cast at h3; linarith
  have hlogs : 0 < log (s : ℝ) := log_pos (by linarith)
  set P := (range (s + 1)).filter Nat.Prime
  have hterm : ∀ p ∈ P, (Nat.primeCounting (x / p) : ℝ) ≤ 4 * C₀ * x / log x * (1 / p) := by
    intro p hp
    simp only [P, mem_filter, mem_range] at hp
    have hpp := hp.2.pos
    have hps : p * s ≤ x := by
      calc p * s ≤ s * s := Nat.mul_le_mul_right _ (by omega)
        _ ≤ x := Nat.sqrt_le x
    have hy : s ≤ x / p := (Nat.le_div_iff_mul_le hpp).mpr (by linarith)
    have hy2 : 2 ≤ x / p := by omega
    have hpi := pi_le_div_log (x / p) hy2
    have hyR : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / p := Nat.cast_div_le
    have hyS : (s : ℝ) ≤ ((x / p : ℕ) : ℝ) := by exact_mod_cast hy
    have hlogy : log (s : ℝ) ≤ log ((x / p : ℕ) : ℝ) := log_le_log (by linarith) hyS
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp
    calc (Nat.primeCounting (x / p) : ℝ) ≤ C₀ * ((x / p : ℕ) : ℝ) / log ((x / p : ℕ) : ℝ) := hpi
      _ ≤ C₀ * ((x : ℝ) / p) / (log (x : ℝ) / 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hyR hC₀.le)
            (by positivity) (by linarith)
      _ = 4 * C₀ * x / log x * (1 / p) := by field_simp
  have hPsub : P ⊆ (range (2 ^ J + 1)).filter Nat.Prime := by
    intro p hp
    simp only [P, mem_filter, mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    have h1 : s ≤ x := Nat.sqrt_le_self x
    have h2 : x < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) x
    omega
  have hsum : ∑ p ∈ P, (1 : ℝ) / p ≤ 2 * C₀ / log 2 * (1 + log J) := by
    refine le_trans ?_ (sum_inv_primes_le J)
    exact sum_le_sum_of_subset_of_nonneg hPsub (fun _ _ _ => by positivity)
  calc (((range (x + 1)).filter IsSemiprime).card : ℝ)
      ≤ ((∑ p ∈ P, Nat.primeCounting (x / p) : ℕ) : ℝ) := by exact_mod_cast semiprime_count_le x
    _ = ∑ p ∈ P, (Nat.primeCounting (x / p) : ℝ) := by push_cast; rfl
    _ ≤ ∑ p ∈ P, 4 * C₀ * x / log x * (1 / (p : ℝ)) := sum_le_sum hterm
    _ = 4 * C₀ * x / log x * ∑ p ∈ P, (1 : ℝ) / p := by rw [mul_sum]
    _ ≤ 4 * C₀ * x / log x * (2 * C₀ / log 2 * (1 + log J)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * C₀ * (2 * C₀ / log 2) * x * (1 + log J) / log x := by ring

end Semiprimes

/-! ## Density bookkeeping -/

theorem density_zero_or {p r : ℕ → Prop} [DecidablePred p] [DecidablePred r]
    (hp : Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop (𝓝 0))
    (hr : Tendsto (fun N : ℕ => (Nat.count r N : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Nat.count (fun n => p n ∨ r n) N : ℝ) / N) atTop (𝓝 0) := by
  have hsum := hp.add hr
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun N => by positivity) (fun N => ?_)
  rw [← add_div]
  have : Nat.count (fun n => p n ∨ r n) N ≤ Nat.count p N + Nat.count r N := by
    simp only [Nat.count_eq_card_filter_range, Finset.filter_or]
    exact Finset.card_union_le _ _
  have hR : (Nat.count (fun n => p n ∨ r n) N : ℝ) ≤ (Nat.count p N : ℝ) + Nat.count r N := by
    exact_mod_cast this
  exact div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)

theorem count_le_count_add {p r E : ℕ → Prop} [DecidablePred p] [DecidablePred r]
    [DecidablePred E] (h : ∀ n, ¬ E n → (p n ↔ r n)) (N : ℕ) :
    Nat.count p N ≤ Nat.count r N + Nat.count E N := by
  calc Nat.count p N ≤ Nat.count (fun n => r n ∨ E n) N :=
        Nat.count_mono_left fun k _ hk => by
          by_cases hE : E k
          · exact Or.inr hE
          · exact Or.inl ((h k hE).mp hk)
    _ ≤ Nat.count r N + Nat.count E N := by
        simp only [Nat.count_eq_card_filter_range, Finset.filter_or]
        exact Finset.card_union_le _ _

/-- Two sets that agree outside a density-zero set `E` have the same density. -/
theorem tendsto_density_of_eq_off {p r E : ℕ → Prop} [DecidablePred p] [DecidablePred r]
    [DecidablePred E] (h : ∀ n, ¬ E n → (p n ↔ r n)) {d : ℝ}
    (hE : Tendsto (fun N : ℕ => (Nat.count E N : ℝ) / N) atTop (𝓝 0))
    (hr : Tendsto (fun N : ℕ => (Nat.count r N : ℝ) / N) atTop (𝓝 d)) :
    Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop (𝓝 d) := by
  have hlo := hr.sub hE
  have hhi := hr.add hE
  rw [sub_zero] at hlo
  rw [add_zero] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun N => ?_) (fun N => ?_)
  · simp only
    rw [← sub_div]
    have := count_le_count_add (p := r) (r := p) (E := E) (fun n hn => (h n hn).symm) N
    have : (Nat.count r N : ℝ) ≤ Nat.count p N + Nat.count E N := by exact_mod_cast this
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · simp only
    rw [← add_div]
    have := count_le_count_add h N
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) (Nat.cast_nonneg _)

/-- A set of density `d > 0` has `nth k / k → 1/d`. -/
theorem tendsto_nth_div_of_density (p : ℕ → Prop) [DecidablePred p] {d : ℝ} (hd : 0 < d)
    (h : Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop (𝓝 d)) :
    Tendsto (fun k : ℕ => (Nat.nth p k : ℝ) / k) atTop (𝓝 (1 / d)) := by
  have hinf : (Set.ofPred p).Infinite := by
    intro hfin
    have h0 : Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat (hfin.toFinset.card : ℝ))
        (fun N => by positivity) (fun N => ?_)
      have := Nat.count_le_card hfin N
      have hR : (Nat.count p N : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast this
      exact div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)
    exact hd.ne' (tendsto_nhds_unique h h0)
  have hmono := Nat.nth_strictMono hinf
  have hcomp := h.comp hmono.tendsto_atTop
  have e : (fun N : ℕ => (Nat.count p N : ℝ) / N) ∘ Nat.nth p = fun k : ℕ => (k : ℝ) / (Nat.nth p k : ℝ) := by
    funext k; simp [Nat.count_nth_of_infinite hinf]
  rw [e] at hcomp
  have := hcomp.inv₀ hd.ne'
  rw [one_div]
  refine this.congr fun k => ?_
  simp only [inv_div]

end OpenProblemsLib.PNTApps
