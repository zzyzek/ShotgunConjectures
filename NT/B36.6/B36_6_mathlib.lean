/-
Guy B36 (Ecker), Mathlib proof of the README result.

README result: Σ φ(n)/n^x and Σ (-1)^(n+1) φ(n)/n^x (x real) both converge
exactly for x > 2.

Main theorem `B36_6_main`: for every real x,
(Σ φ(n)/n^x summable ↔ 2 < x) ∧ ((∃ L, Σ_{n<N} (-1)^(n+1) φ(n)/n^x → L) ↔ 2 < x)
(φ = Mathlib `Nat.totient`; the first series has nonnegative terms, so summable = convergent;
for the alternating series convergence means convergence of the partial sums).

Proved here:
- `B36_6_first`: Σ φ(n)/n^x is summable iff x > 2. Proof: φ(n)/n^x ≤ 1/n^(x-1),
  and for x ≤ 2, φ(p)/p^x ≥ 1/(2p) on primes, whose reciprocal sum diverges
  (Mathlib `not_summable_one_div_on_primes`).
- `B36_6_alt_conv`: for x > 2 the alternating series is (absolutely) summable.
- `B36_6_alt_div`: for x ≤ 1 its partial sums do not converge (the terms
  do not tend to 0: |term| ≥ 1/2 at every prime).
- `alt_div_le_two`: for 0 < x ≤ 2 its partial sums do not converge. Proof: the mean value
  A(N) = Σ_{n<N} (-1)^(n+1) φ(n) ≥ N²/40 - (5/4)N - (N log N)/2 (`A_lower`: φ(n) ≤ n/2 for even
  n; φ(n) ≥ n - Σ_{p ∣ n} n/p for odd n, with Σ_{k ≥ 3} 1/k² ≤ 2/5 and the harmonic bound);
  Kronecker's lemma (`kronecker`, by summation by parts) would give A(N)/N^x → 0, hence
  A(N)/N² → 0.
- `B36_6_alt_iff`, `B36_6_main`: the two equivalences.

Outside Lean: nothing.
-/
import Mathlib

open Filter Topology

theorem B36_6_first (x : ℝ) :
    Summable (fun n : ℕ => (n.totient : ℝ) / (n : ℝ) ^ x) ↔ 2 < x := by
  constructor
  · intro h
    by_contra hx
    push Not at hx
    apply not_summable_one_div_on_primes
    refine (h.mul_left 2).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · by_cases hp : n.Prime
      · rw [Set.indicator_of_mem (show n ∈ {p | p.Prime} from hp)]
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
        have hn1 : (1 : ℝ) ≤ n := by linarith
        have hpow : (n : ℝ) ^ x ≤ (n : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hx
        rw [Real.rpow_two] at hpow
        have hpos : 0 < (n : ℝ) ^ x := by positivity
        rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one,
          div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hpos]
        nlinarith
      · rw [Set.indicator_of_notMem (show n ∉ {p | p.Prime} from hp)]
        positivity
  · intro hx
    have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (x - 1)) :=
      Real.summable_one_div_nat_rpow.mpr (by linarith)
    refine hs.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.totient_zero, Nat.cast_zero, zero_div, one_div]
      positivity
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hle : (n.totient : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (n.totient : ℝ) * (n : ℝ) ^ (x - 1) ≤ n * (n : ℝ) ^ (x - 1) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (n : ℝ) ^ x := by
          rw [Real.rpow_sub hn', Real.rpow_one]
          field_simp

theorem B36_6_alt_conv (x : ℝ) (hx : 2 < x) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x) := by
  refine Summable.of_norm ((B36_6_first x).mpr hx |>.congr (fun n => ?_))
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, Real.norm_of_nonneg (by positivity)]

theorem B36_6_alt_div (x : ℝ) (hx : x ≤ 1) :
    ¬ ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  set a := fun n : ℕ => (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x with ha
  have hterm : Tendsto a atTop (𝓝 0) := by
    have h1 := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
    rw [sub_self] at h1
    refine h1.congr (fun N => ?_)
    simp [Finset.sum_range_succ, ha]
  have hev := (hterm.norm).eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < 1 / 2 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have h := hN p hpN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hpow : (p : ℝ) ^ x ≤ (p : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 hx
  rw [Real.rpow_one] at hpow
  have hpos : 0 < (p : ℝ) ^ x := by positivity
  simp only [ha, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, Real.norm_of_nonneg hpos.le] at h
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one, div_lt_iff₀ hpos] at h
  nlinarith

open Finset

/-! ### Divergence of the alternating series for 0 < x ≤ 2 -/

/-- n ≤ φ(n) + Σ_{p ∣ n} n/p (union bound on the non-coprime residues). -/
theorem bonf (n : ℕ) : n ≤ n.totient + ∑ p ∈ n.primeFactors, n / p := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · simp [h0]
  have hI : (Ioc 0 n).card = n := by simp
  have hcop : ((Ioc 0 n).filter (fun x => n.Coprime x)).card = n.totient := by
    have := Nat.filter_coprime_Ico_eq_totient n 1
    rw [show Ico 1 (1 + n) = Ioc 0 n by ext x; simp only [mem_Ico, mem_Ioc]; omega] at this
    exact this
  have hsub : (Ioc 0 n).filter (fun x => ¬ n.Coprime x) ⊆
      n.primeFactors.biUnion (fun p => (Ioc 0 n).filter (fun x => p ∣ x)) := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_biUnion]
    set g := Nat.gcd n x
    have hg1 : g ≠ 1 := hx.2
    refine ⟨g.minFac, ?_, mem_filter.mpr ⟨hx.1, ?_⟩⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨Nat.minFac_prime hg1, (Nat.minFac_dvd g).trans (Nat.gcd_dvd_left n x), by omega⟩
    · exact (Nat.minFac_dvd g).trans (Nat.gcd_dvd_right n x)
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le (s := n.primeFactors) (t := fun p => (Ioc 0 n).filter (fun x => p ∣ x))
  simp only [Nat.Ioc_filter_dvd_card_eq_div] at h2
  have h3 := card_filter_add_card_filter_not (s := Ioc 0 n) (fun x => n.Coprime x)
  rw [hcop, hI] at h3
  omega

theorem odd_sum (N : ℕ) : ∑ n ∈ range N, (if Odd n then n else 0) = (N / 2) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd N with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have : ¬ Odd (t + t) := Nat.not_odd_iff_even.mpr ⟨t, rfl⟩
      simp only [this, ite_false]
      rw [show (t + t) / 2 = t by omega, show (t + t + 1) / 2 = t by omega]; ring
    · simp only [show Odd (2 * t + 1) from ⟨t, rfl⟩, ite_true]
      rw [show (2 * t + 1) / 2 = t by omega,
        show (2 * t + 1 + 1) / 2 = t + 1 by omega]; ring

theorem sum_range_real (N : ℕ) : ∑ n ∈ range N, (n : ℝ) = (N : ℝ) * (N - 1) / 2 := by
  have h := Finset.sum_range_id_mul_two N
  have : ((∑ i ∈ range N, i : ℕ) : ℝ) * 2 = (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  rw [Nat.cast_sub hN, Nat.cast_one] at this
  push_cast at this
  linarith

theorem even_sum_le (N : ℕ) :
    ∑ n ∈ range N, (if Even n then (n : ℝ) else 0) ≤ (N : ℝ) ^ 2 / 4 := by
  have hsplit : ∑ n ∈ range N, (n : ℝ) = ∑ n ∈ range N, (if Even n then (n : ℝ) else 0) +
      ∑ n ∈ range N, (if Odd n then (n : ℝ) else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun n _ => ?_)
    rcases Nat.even_or_odd n with h | h
    · have : ¬ Odd n := Nat.not_odd_iff_even.mpr h
      simp [h, this]
    · have : ¬ Even n := Nat.not_even_iff_odd.mpr h
      simp [h, this]
  have ho : ∑ n ∈ range N, (if Odd n then (n : ℝ) else 0) = (((N / 2) ^ 2 : ℕ) : ℝ) := by
    rw [← odd_sum]; push_cast; refine sum_congr rfl (fun n _ => ?_); split_ifs <;> simp
  rw [sum_range_real, ho] at hsplit
  have h2 : (N : ℝ) - 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) := by
    have : N ≤ 2 * (N / 2) + 1 := by omega
    have : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have h3 : (0 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  push_cast at hsplit
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h4 : ((N : ℝ) - 1) ^ 2 ≤ (2 * ((N / 2 : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ hN1 h2 2
  nlinarith

/-- Σ_{3 ≤ k < N} 1/k² ≤ 2/5 (telescoping with 1/k² ≤ 1/(k - 1/2) - 1/(k + 1/2)). -/
theorem inv_sq_sum (N : ℕ) : ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) ^ 2 else 0) ≤ 2 / 5 := by
  have key : ∀ N, 3 ≤ N →
      ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) ^ 2 else 0) ≤ 2 / 5 - 1 / ((N : ℝ) - 1 / 2) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [sum_range_succ]; norm_num
    | succ N hN ih =>
      rw [sum_range_succ]
      simp only [hN, ite_true]
      have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have : 1 / (N : ℝ) ^ 2 ≤ 1 / ((N : ℝ) - 1 / 2) - 1 / (((N + 1 : ℕ) : ℝ) - 1 / 2) := by
        push_cast
        rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith
      linarith
  rcases Nat.lt_or_ge N 3 with h | h
  · rw [sum_eq_zero (fun k hk => by
      rw [mem_range] at hk; simp only [show ¬ 3 ≤ k by omega, ite_false])]
    norm_num
  · have := key N h
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast h
    have : 0 < 1 / ((N : ℝ) - 1 / 2) := by apply div_pos one_pos; linarith
    linarith

theorem harm_sum (N : ℕ) : ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) else 0) ≤ 1 + Real.log N := by
  have h1 : ∀ M, ∑ k ∈ range (M + 1), (if 1 ≤ k then 1 / (k : ℝ) else 0) = (harmonic M : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ, ih, harmonic_succ]
      simp only [show 1 ≤ M + 1 by omega, ite_true]
      push_cast; ring
  calc ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) else 0)
      ≤ ∑ k ∈ range (N + 1), (if 1 ≤ k then 1 / (k : ℝ) else 0) := by
        rw [sum_range_succ]
        have : ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) else 0) ≤
            ∑ k ∈ range N, (if 1 ≤ k then 1 / (k : ℝ) else 0) := by
          apply sum_le_sum; intro k _
          split_ifs <;> first | exact le_rfl | (positivity) | omega
        have : (0 : ℝ) ≤ (if 1 ≤ N then 1 / (N : ℝ) else 0) := by split_ifs <;> positivity
        linarith
    _ = harmonic N := h1 N
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

theorem totient_add_half_le (n : ℕ) (he : Even n) : n.totient + n / 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp
    · exact absurd he (by decide)
  have hsub : (range n).filter (fun a => n.Coprime a) ⊆
      (Ioc 0 n).filter (fun a => ¬ 2 ∣ a) := by
    intro a ha
    simp only [mem_filter, mem_range, mem_Ioc] at ha ⊢
    refine ⟨⟨?_, by omega⟩, fun h2a => ?_⟩
    · rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0, Nat.coprime_zero_right] at ha; omega
      · exact h0
    · have := Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.mp he) ha.2
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp this h2a
  have hc := card_filter_add_card_filter_not (s := Ioc 0 n) (fun a => 2 ∣ a)
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc] at hc
  have := card_le_card hsub
  rw [← Nat.totient_eq_card_coprime] at this
  omega

/-- For odd k ≥ 1: Σ_{n<N, n odd, k ∣ n} n/k = (c/2)², c = ⌈N/k⌉. -/
theorem odd_mult_sum (N k : ℕ) (hk : Odd k) :
    ∑ n ∈ range N, (if Odd n ∧ k ∣ n then n / k else 0) = ((N + k - 1) / k / 2) ^ 2 := by
  have hk0 : 0 < k := hk.pos
  set c := (N + k - 1) / k
  have e : (range N).filter (fun n => Odd n ∧ k ∣ n) = ((range c).filter Odd).image (k * ·) := by
    ext n
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hn, ho, ⟨j, rfl⟩⟩
      refine ⟨j, ⟨?_, (Nat.odd_mul.mp ho).2⟩, rfl⟩
      have : j + 1 ≤ c := by
        rw [Nat.le_div_iff_mul_le hk0, show (j + 1) * k = k * j + k by ring]; omega
      omega
    · rintro ⟨j, ⟨hj, ho⟩, rfl⟩
      refine ⟨?_, Nat.odd_mul.mpr ⟨hk, ho⟩, ⟨j, rfl⟩⟩
      have := (Nat.le_div_iff_mul_le hk0).mp (show j + 1 ≤ c by omega)
      rw [show (j + 1) * k = k * j + k by ring] at this; omega
  rw [← sum_filter, e, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hk0 h)]
  rw [← odd_sum c, sum_filter]
  refine sum_congr rfl (fun j _ => ?_)
  rw [Nat.mul_div_cancel_left _ hk0]

/-- Σ_{n<N} (-1)^(n+1) φ(n) ≥ N²/40 - (5/4)N - (N log N)/2. -/
theorem A_lower (N : ℕ) :
    (N : ℝ) ^ 2 / 40 - 5 / 4 * N - N * Real.log N / 2 ≤
      ∑ n ∈ range N, (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) := by
  set O := ∑ n ∈ range N, (if Odd n then (n.totient : ℝ) else 0)
  set E := ∑ n ∈ range N, (if Even n then (n.totient : ℝ) else 0)
  have hA : ∑ n ∈ range N, (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) = O - E := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun n _ => ?_)
    rcases Nat.even_or_odd n with h | h
    · have h' : ¬ Odd n := Nat.not_odd_iff_even.mpr h
      have : Odd (n + 1) := h.add_one
      simp [h, h', this.neg_one_pow]
    · have h' : ¬ Even n := Nat.not_even_iff_odd.mpr h
      have : Even (n + 1) := h.add_one
      simp [h, h', this.neg_one_pow]
  -- even part
  have hE : E ≤ (N : ℝ) ^ 2 / 8 := by
    calc E ≤ ∑ n ∈ range N, (1 / 2 : ℝ) * (if Even n then (n : ℝ) else 0) := by
          apply sum_le_sum; intro n _
          by_cases h : Even n
          · simp only [h, ite_true]
            have h1 := totient_add_half_le n h
            have h2 : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 :=
              Nat.cast_div (even_iff_two_dvd.mp h) (by norm_num)
            have : ((n.totient + n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
            push_cast at this; rw [h2] at this; linarith
          · simp [h]
      _ = (1 / 2) * ∑ n ∈ range N, (if Even n then (n : ℝ) else 0) := by rw [mul_sum]
      _ ≤ (1 / 2) * ((N : ℝ) ^ 2 / 4) := by
          apply mul_le_mul_of_nonneg_left (even_sum_le N) (by norm_num)
      _ = (N : ℝ) ^ 2 / 8 := by ring
  -- odd part via Bonferroni
  set G : ℕ → ℕ → ℝ := fun n k =>
    if (3 ≤ k ∧ Odd k) ∧ (Odd n ∧ k ∣ n) then ((n / k : ℕ) : ℝ) else 0 with hG
  have hterm : ∀ n ∈ range N, (if Odd n then (n : ℝ) else 0) ≤
      (if Odd n then (n.totient : ℝ) else 0) + ∑ k ∈ range N, G n k := by
    intro n hn
    rw [mem_range] at hn
    by_cases ho : Odd n
    · simp only [ho, ite_true]
      have h1 := bonf n
      have hsub : n.primeFactors ⊆ (range N).filter (fun k => (3 ≤ k ∧ Odd k) ∧ (Odd n ∧ k ∣ n)) := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        have hp2 : p ≠ 2 := by
          intro h; rw [h] at hpd; exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpd)
        have hle : p ≤ n := Nat.le_of_dvd ho.pos hpd
        simp only [mem_filter, mem_range]
        exact ⟨by omega, ⟨by have := hpp.two_le; omega, hpp.odd_of_ne_two hp2⟩, ho, hpd⟩
      have h2 := sum_le_sum_of_subset (f := fun k => n / k) hsub
      rw [sum_filter] at h2
      have h3 : ((n : ℕ) : ℝ) ≤ ((n.totient + ∑ k ∈ range N,
          (if (3 ≤ k ∧ Odd k) ∧ (Odd n ∧ k ∣ n) then n / k else 0) : ℕ) : ℝ) := by
        exact_mod_cast (le_trans h1 (Nat.add_le_add_left h2 _))
      push_cast at h3
      simp only [hG]
      convert h3 using 2
    · simp only [ho, ite_false, zero_add]
      apply sum_nonneg; intro k _; simp only [hG]; split_ifs <;> positivity
  have hO : ∑ n ∈ range N, (if Odd n then (n : ℝ) else 0) ≤
      O + ∑ k ∈ range N, (if 3 ≤ k then ((N : ℝ) / k + 1) ^ 2 / 4 else 0) := by
    calc ∑ n ∈ range N, (if Odd n then (n : ℝ) else 0)
        ≤ ∑ n ∈ range N, ((if Odd n then (n.totient : ℝ) else 0) + ∑ k ∈ range N, G n k) :=
          sum_le_sum hterm
      _ = O + ∑ k ∈ range N, ∑ n ∈ range N, G n k := by rw [sum_add_distrib, sum_comm]
      _ ≤ O + ∑ k ∈ range N, (if 3 ≤ k then ((N : ℝ) / k + 1) ^ 2 / 4 else 0) := by
          apply add_le_add le_rfl
          apply sum_le_sum; intro k _
          by_cases hc : 3 ≤ k ∧ Odd k
          · have hk0 : (0 : ℝ) < k := by have := hc.1; exact_mod_cast (show 0 < k by omega)
            have e : ∑ n ∈ range N, G n k =
                ((∑ n ∈ range N, (if Odd n ∧ k ∣ n then n / k else 0) : ℕ) : ℝ) := by
              push_cast
              refine sum_congr rfl (fun n _ => ?_)
              simp only [hG, hc, true_and]
            rw [e, odd_mult_sum N k hc.2]
            simp only [hc.1, ite_true]
            set c := (N + k - 1) / k
            have hc1 : (c : ℝ) ≤ (N : ℝ) / k + 1 := by
              have : (c : ℝ) ≤ ((N + k - 1 : ℕ) : ℝ) / k := Nat.cast_div_le
              have h2 : ((N + k - 1 : ℕ) : ℝ) ≤ (N : ℝ) + k := by
                have : N + k - 1 ≤ N + k := by omega
                exact_mod_cast this
              calc (c : ℝ) ≤ ((N + k - 1 : ℕ) : ℝ) / k := this
                _ ≤ ((N : ℝ) + k) / k := div_le_div_of_nonneg_right h2 hk0.le
                _ = (N : ℝ) / k + 1 := by field_simp
            have hc2 : ((c / 2 : ℕ) : ℝ) ≤ ((N : ℝ) / k + 1) / 2 := by
              have : ((c / 2 : ℕ) : ℝ) ≤ (c : ℝ) / 2 := Nat.cast_div_le
              linarith
            push_cast
            have : ((c / 2 : ℕ) : ℝ) ^ 2 ≤ (((N : ℝ) / k + 1) / 2) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hc2 2
            linarith
          · have : ∑ n ∈ range N, G n k = 0 := by
              apply sum_eq_zero; intro n _; simp only [hG]
              simp only [show ¬ ((3 ≤ k ∧ Odd k) ∧ Odd n ∧ k ∣ n) from fun h => hc h.1, ite_false]
            rw [this]; split_ifs <;> positivity
  -- the sum over k
  have hD : ∑ k ∈ range N, (if 3 ≤ k then ((N : ℝ) / k + 1) ^ 2 / 4 else 0) ≤
      (N : ℝ) ^ 2 / 4 * (2 / 5) + (N : ℝ) / 2 * (1 + Real.log N) + 1 / 4 * N := by
    have e : ∑ k ∈ range N, (if 3 ≤ k then ((N : ℝ) / k + 1) ^ 2 / 4 else 0) =
        (N : ℝ) ^ 2 / 4 * ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) ^ 2 else 0) +
        (N : ℝ) / 2 * ∑ k ∈ range N, (if 3 ≤ k then 1 / (k : ℝ) else 0) +
        1 / 4 * ∑ k ∈ range N, (if 3 ≤ k then (1 : ℝ) else 0) := by
      rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl (fun k _ => ?_)
      split_ifs with h
      · have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
        ring
      · simp
    rw [e]
    have h1 := inv_sq_sum N
    have h2 := harm_sum N
    have h3 : ∑ k ∈ range N, (if 3 ≤ k then (1 : ℝ) else 0) ≤ N := by
      calc ∑ k ∈ range N, (if 3 ≤ k then (1 : ℝ) else 0) ≤ ∑ k ∈ range N, (1 : ℝ) := by
            apply sum_le_sum; intro k _; split_ifs <;> norm_num
        _ = N := by simp
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (N : ℝ) ^ 2 / 4 by positivity)
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (N : ℝ) / 2 by positivity)
    linarith
  -- assemble
  have hodd : ((N : ℝ) ^ 2 - 2 * N) / 4 ≤ ∑ n ∈ range N, (if Odd n then (n : ℝ) else 0) := by
    have e : ∑ n ∈ range N, (if Odd n then (n : ℝ) else 0) = (((N / 2) ^ 2 : ℕ) : ℝ) := by
      rw [← odd_sum]; push_cast; refine sum_congr rfl (fun n _ => ?_); split_ifs <;> simp
    rw [e]; push_cast
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0; norm_num
    have h2 : ((N : ℝ) - 1) / 2 ≤ ((N / 2 : ℕ) : ℝ) := by
      have : N ≤ 2 * (N / 2) + 1 := by omega
      have : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    have : (0 : ℝ) ≤ ((N : ℝ) - 1) / 2 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have := pow_le_pow_left₀ this h2 2
    nlinarith
  rw [hA]
  nlinarith [hE, hO, hD, hodd]


/-- Summation by parts: Σ_{n<N} w_n b_n = w_N S_N - Σ_{n<N} (w_{n+1} - w_n) S_{n+1}. -/
theorem abel_id (w b : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, w n * b n = w N * (∑ m ∈ range N, b m) -
      ∑ n ∈ range N, (w (n + 1) - w n) * (∑ m ∈ range (n + 1), b m) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun n => (w (n + 1) - w n) * _), sum_range_succ b]
    ring

/-- Weighted Cesàro: Δ ≥ 0 with Σ_{n<N} Δ_n ≤ w_N → ∞ and ε → 0 give (Σ_{n<N} Δ_n ε_n)/w_N → 0. -/
theorem wcesaro (w Δ ε : ℕ → ℝ) (hΔ : ∀ n, 0 ≤ Δ n)
    (hsum : ∀ M N, M ≤ N → ∑ n ∈ Ico M N, Δ n ≤ w N)
    (hinf : Tendsto w atTop atTop) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun N => (∑ n ∈ range N, Δ n * ε n) / w N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hε (δ / 2) (by linarith)
  set C := ∑ n ∈ range M, Δ n * |ε n|
  have hC : 0 ≤ C := sum_nonneg (fun n _ => mul_nonneg (hΔ n) (abs_nonneg _))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((tendsto_atTop.mp hinf) (2 * C / δ + 1))
  refine ⟨max M N₀, fun N hN => ?_⟩
  have hNM : M ≤ N := le_of_max_le_left hN
  have hwN : 2 * C / δ + 1 ≤ w N := hN₀ N (le_of_max_le_right hN)
  have hwpos : 0 < w N := by have : 0 ≤ 2 * C / δ := by positivity
                             linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hwpos, div_lt_iff₀ hwpos]
  rw [← sum_range_add_sum_Ico _ hNM]
  have h1 : |∑ n ∈ range M, Δ n * ε n| ≤ C := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl (fun n _ => ?_)))
    rw [abs_mul, abs_of_nonneg (hΔ n)]
  have h2 : |∑ n ∈ Ico M N, Δ n * ε n| ≤ δ / 2 * w N := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Ico M N, |Δ n * ε n| ≤ ∑ n ∈ Ico M N, Δ n * (δ / 2) := by
          apply sum_le_sum; intro n hn
          rw [abs_mul, abs_of_nonneg (hΔ n)]
          apply mul_le_mul_of_nonneg_left _ (hΔ n)
          have := hM n (mem_Ico.mp hn).1
          rw [Real.dist_eq, sub_zero] at this
          exact this.le
      _ = (∑ n ∈ Ico M N, Δ n) * (δ / 2) := by rw [sum_mul]
      _ ≤ w N * (δ / 2) := mul_le_mul_of_nonneg_right (hsum M N hNM) (by linarith)
      _ = δ / 2 * w N := by ring
  have h3 : 2 * C < δ * w N := by
    have := mul_le_mul_of_nonneg_left hwN hδ.le
    rw [mul_add, mul_div_cancel₀ _ hδ.ne'] at this
    linarith
  calc |∑ n ∈ range M, Δ n * ε n + ∑ n ∈ Ico M N, Δ n * ε n|
      ≤ |∑ n ∈ range M, Δ n * ε n| + |∑ n ∈ Ico M N, Δ n * ε n| := abs_add_le _ _
    _ ≤ C + δ / 2 * w N := add_le_add h1 h2
    _ < δ * w N := by linarith

/-- Kronecker's lemma: if Σ b_n converges and 0 ≤ w is monotone with w → ∞, then
(Σ_{n<N} w_n b_n)/w_N → 0. -/
theorem kronecker (w b : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hmono : Monotone w)
    (hinf : Tendsto w atTop atTop) (L : ℝ)
    (hS : Tendsto (fun N => ∑ n ∈ range N, b n) atTop (𝓝 L)) :
    Tendsto (fun N => (∑ n ∈ range N, w n * b n) / w N) atTop (𝓝 0) := by
  set S := fun N => ∑ n ∈ range N, b n
  set Δ := fun n => w (n + 1) - w n
  set ε := fun n => S (n + 1) - L
  have hΔ : ∀ n, 0 ≤ Δ n := fun n => sub_nonneg.mpr (hmono (Nat.le_succ n))
  have htel : ∀ N, ∑ n ∈ range N, Δ n = w N - w 0 := fun N => sum_range_sub w N
  have hsum : ∀ M N, M ≤ N → ∑ n ∈ Ico M N, Δ n ≤ w N := by
    intro M N hMN
    have := sum_range_add_sum_Ico Δ hMN
    rw [htel, htel] at this
    have := hw0 M
    linarith
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := (hS.comp (tendsto_add_atTop_nat 1)).sub_const L
    rw [sub_self] at this
    exact this
  have key : ∀ N, (∑ n ∈ range N, w n * b n) =
      w N * (S N - L) + L * w 0 - ∑ n ∈ range N, Δ n * ε n := by
    intro N
    rw [abel_id]
    have : ∑ n ∈ range N, Δ n * ε n =
        ∑ n ∈ range N, (w (n + 1) - w n) * (∑ m ∈ range (n + 1), b m) - L * (w N - w 0) := by
      rw [← htel, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl (fun n _ => ?_)
      simp only [Δ, ε, S]; ring
    rw [this]; simp only [S]; ring
  have hpos : ∀ᶠ N in atTop, 0 < w N := hinf.eventually_gt_atTop 0
  have e : ∀ᶠ N in atTop, (∑ n ∈ range N, w n * b n) / w N =
      (S N - L) + L * w 0 / w N - (∑ n ∈ range N, Δ n * ε n) / w N := by
    filter_upwards [hpos] with N hN
    rw [key N]; field_simp
  rw [tendsto_congr' e]
  have t1 : Tendsto (fun N => S N - L) atTop (𝓝 0) := by
    have := hS.sub_const L; rwa [sub_self] at this
  have t2 : Tendsto (fun N => L * w 0 / w N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hinf
  have t3 := wcesaro w Δ ε hΔ hsum hinf hε
  have := (t1.add t2).sub t3
  simpa using this

theorem alt_div_le_two (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 2) :
    ¬ ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  set w : ℕ → ℝ := fun n => (n : ℝ) ^ x
  set A : ℕ → ℝ := fun N => ∑ n ∈ range N, (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ)
  have hw0 : ∀ n, 0 ≤ w n := fun n => by positivity
  have hmono : Monotone w := fun m n h =>
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) hx0.le
  have hinf : Tendsto w atTop atTop := (tendsto_rpow_atTop hx0).comp tendsto_natCast_atTop_atTop
  have hK := kronecker w (fun n => (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x)
    hw0 hmono hinf L (by simpa only [mul_div_assoc] using hL)
  have hwb : ∀ N, ∑ n ∈ range N, w n * ((-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x) = A N := by
    intro N
    refine sum_congr rfl (fun n _ => ?_)
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp
    · have : (n : ℝ) ^ x ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hn) x).ne'
      simp only [w]; field_simp
  simp only [hwb] at hK
  -- A(N)/N² → 0
  have hA2 : Tendsto (fun N : ℕ => A N / (N : ℝ) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hK.norm)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwpos : 0 < w N := Real.rpow_pos_of_pos (by linarith) x
    have hle : w N ≤ (N : ℝ) ^ 2 := by
      simp only [w]
      calc (N : ℝ) ^ x ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hx
        _ = (N : ℝ) ^ 2 := Real.rpow_two _
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2), abs_of_pos hwpos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hwpos hle
  -- but A(N)/N² ≥ 1/40 - o(1)
  have hlog : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlow : Tendsto (fun N : ℕ => (1 : ℝ) / 40 - 5 / 4 * (1 / N) - Real.log N / N / 2)
      atTop (𝓝 (1 / 40)) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ) / 40)).sub (hinv.const_mul (5 / 4))).sub
      (hlog.div_const 2)
    simpa using this
  have ev1 := hlow.eventually (lt_mem_nhds (show (1 : ℝ) / 80 < 1 / 40 by norm_num))
  have ev2 := hA2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 80 by norm_num))
  obtain ⟨N, hN⟩ := (ev1.and (ev2.and (eventually_ge_atTop 1))).exists
  obtain ⟨h1, h2, h3⟩ := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h3
  have hNpos : (0 : ℝ) < N := by linarith
  have hb := A_lower N
  have : (1 : ℝ) / 40 - 5 / 4 * (1 / N) - Real.log N / N / 2 ≤ A N / (N : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e : ((1 : ℝ) / 40 - 5 / 4 * (1 / N) - Real.log N / N / 2) * (N : ℝ) ^ 2 =
        (N : ℝ) ^ 2 / 40 - 5 / 4 * N - N * Real.log N / 2 := by field_simp
    rw [e]; exact hb
  linarith

theorem B36_6_alt_iff (x : ℝ) :
    (∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x) atTop (𝓝 L)) ↔ 2 < x := by
  constructor
  · intro h
    by_contra hx
    push Not at hx
    rcases le_or_gt x 1 with h1 | h1
    · exact B36_6_alt_div x h1 h
    · exact alt_div_le_two x (by linarith) hx h
  · intro hx
    exact ⟨_, (B36_6_alt_conv x hx).hasSum.tendsto_sum_nat⟩

theorem B36_6_main (x : ℝ) :
    (Summable (fun n : ℕ => (n.totient : ℝ) / (n : ℝ) ^ x) ↔ 2 < x) ∧
    ((∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (-1 : ℝ) ^ (n + 1) * (n.totient : ℝ) / (n : ℝ) ^ x) atTop (𝓝 L)) ↔ 2 < x) :=
  ⟨B36_6_first x, B36_6_alt_iff x⟩
