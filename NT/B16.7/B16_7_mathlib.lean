/-
Guy B16 (Panaitopol), Mathlib proof.

Main theorems:
- `B16_7_gap`: for every k ≥ 1 there is m such that m and m + k are squarefree
  and m + 1, ..., m + k - 1 are not, i.e. m and m + k are consecutive
  squarefree numbers.
- `B16_7_main`: equivalently, with f_n = `Nat.nth Squarefree n` the n-th
  squarefree number, for every k ≥ 1 there is n with f_(n+1) - f_n = k.
This is the README result (the "positive proportion" remark is not proved).

Proof: take k - 1 distinct primes p_i > k (i = 1, ..., k - 1), and c with
c + i ≡ 0 (mod p_i^2) (Chinese remainder theorem, Mathlib
`Nat.chineseRemainderOfFinset`); Q = ∏ p_i^2. For m = c + Q j the numbers
m + i are not squarefree, and p_i^2 divides neither m nor m + k. For every
other prime q, q^2 ∣ m or q^2 ∣ m + k puts j in one class mod q^2 (Q is a
unit mod q^2), at most J/q^2 + 1 values of j < J each. Since
Σ_(q prime) 1/q^2 ≤ 1/4 + 1/9 + 1/8 = 35/72 (telescoping over odd n ≥ 5),
fewer than J of the j < J are excluded once J = 10000 (c + Q + k)^2.

Not checked: nothing.
-/
import Mathlib

open Finset

theorem B16_7_class (d Q c J : ℕ) (hQ : Nat.Coprime Q d) :
    ((range J).filter (fun j => d ∣ c + Q * j)).card ≤ J / d + 1 := by
  have hinj : Set.InjOn (fun j => j / d) ((range J).filter (fun j => d ∣ c + Q * j) : Set ℕ) := by
    intro j1 h1 j2 h2 heq
    simp only [coe_filter, mem_range] at h1 h2
    have a1 : c + Q * j1 ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr h1.2
    have a2 : c + Q * j2 ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr h2.2
    have hm : Q * j1 ≡ Q * j2 [MOD d] := Nat.ModEq.add_left_cancel' c (a1.trans a2.symm)
    have hj : j1 ≡ j2 [MOD d] := Nat.ModEq.cancel_left_of_coprime hQ.symm hm
    simp only at heq
    calc j1 = d * (j1 / d) + j1 % d := (Nat.div_add_mod _ _).symm
      _ = d * (j2 / d) + j2 % d := by rw [heq, hj]
      _ = j2 := Nat.div_add_mod _ _
  have := card_le_card_of_injOn (fun j => j / d) (t := range (J / d + 1)) (by
    intro j hj
    simp only [coe_filter, mem_range] at hj
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hj.1.le)) hinj
  simpa using this

/-- Telescoping majorant for the tail of Σ 1/q^2. -/
noncomputable def B16_7_h (N : ℕ) : ℝ :=
  if N % 2 = 1 then 1 / (2 * ((N : ℝ) - 1)) else 1 / (2 * (N : ℝ))

theorem B16_7_sum_aux (N : ℕ) (hN : 5 ≤ N) :
    ∑ q ∈ (range N).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 35 / 72 - B16_7_h N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [show (range 5).filter Nat.Prime = {2, 3} by decide]
    norm_num [B16_7_h]
  | succ N hN ih =>
    have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN
    rw [range_add_one, filter_insert]
    have hstep : B16_7_h (N + 1) ≤ B16_7_h N := by
      unfold B16_7_h
      rcases Nat.mod_two_eq_zero_or_one N with h | h
      · have e1 : (N + 1) % 2 = 1 := by omega
        have e2 : ¬ (N % 2 = 1) := by omega
        simp only [e1, e2, ↓reduceIte]
        push_cast
        apply le_of_eq
        ring_nf
      · have e1 : ¬ ((N + 1) % 2 = 1) := by omega
        simp only [e1, h, ↓reduceIte]
        push_cast
        apply one_div_le_one_div_of_le (by linarith)
        linarith
    split_ifs with hp
    · rw [sum_insert (by simp)]
      have hodd : N % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · omega
        · exact h
      have hdiff : 1 / (N : ℝ) ^ 2 ≤ B16_7_h N - B16_7_h (N + 1) := by
        unfold B16_7_h
        have e1 : ¬ ((N + 1) % 2 = 1) := by omega
        simp only [e1, hodd, ↓reduceIte]
        push_cast
        have ha : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by linarith
        have hb : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by linarith
        rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · linarith

theorem B16_7_sum (N : ℕ) :
    ∑ q ∈ (range N).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 35 / 72 := by
  rcases le_or_gt 5 N with h | h
  · have := B16_7_sum_aux N h
    have h5 : (5 : ℝ) ≤ N := by exact_mod_cast h
    have : 0 ≤ B16_7_h N := by
      unfold B16_7_h
      split_ifs
      · exact div_nonneg zero_le_one (by linarith)
      · positivity
    linarith
  · calc _ ≤ ∑ q ∈ (range 5).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (range_subset_range.mpr h.le))
            (fun _ _ _ => by positivity)
      _ ≤ 35 / 72 := by
          rw [show (range 5).filter Nat.Prime = {2, 3} by decide]
          norm_num

theorem B16_7_gap (k : ℕ) (hk : 1 ≤ k) :
    ∃ m, Squarefree m ∧ Squarefree (m + k) ∧ ∀ i, 0 < i → i < k → ¬ Squarefree (m + i) := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · refine ⟨1, squarefree_one, ?_, fun i h1 h2 => by omega⟩
    exact Nat.prime_two.squarefree
  set t := Finset.Ioo 0 k with ht
  set p : ℕ → ℕ := fun i => Nat.nth Nat.Prime (k + i) with hpdef
  have hpp : ∀ i, (p i).Prime := fun i => Nat.prime_nth_prime _
  have hpk : ∀ i, k < p i := fun i => by
    have := Nat.add_two_le_nth_prime (k + i)
    simp only [hpdef]
    omega
  have hpinj : Function.Injective p := fun a b h => by
    have := Nat.nth_injective Nat.infinite_setOfPred_prime h
    omega
  set s : ℕ → ℕ := fun i => p i ^ 2 with hsdef
  set a : ℕ → ℕ := fun i => p i ^ 2 - i with hadef
  have hs0 : ∀ i ∈ t, s i ≠ 0 := fun i _ => pow_ne_zero 2 (hpp i).ne_zero
  have hcop : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime s) := fun i _ j _ hij =>
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes (hpp i) (hpp j)).mpr (hpinj.ne hij))
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset a s t hs0 hcop
  set Q := ∏ i ∈ t, s i with hQ
  have hQpos : 0 < Q := Finset.prod_pos (fun i _ => pow_pos (hpp i).pos 2)
  have hsq : ∀ i, k < p i ^ 2 := fun i => by
    have := hpk i
    nlinarith
  -- Residues of m = c + Q j modulo p_i^2.
  --
  have hres : ∀ i ∈ t, ∀ j, (c + Q * j) % (p i ^ 2) = p i ^ 2 - i := by
    intro i hi j
    have h1 : c + Q * j ≡ a i + 0 [MOD s i] :=
      (hc i hi).add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_prod_of_mem s hi) j))
    rw [add_zero] at h1
    have hit : 0 < i ∧ i < k := by simpa [ht] using hi
    rw [h1]
    show (p i ^ 2 - i) % (p i ^ 2) = p i ^ 2 - i
    have := hsq i
    exact Nat.mod_eq_of_lt (by omega)
  have hQcop : ∀ q, q.Prime → (∀ i ∈ t, q ≠ p i) → Nat.Coprime Q (q ^ 2) := by
    intro q hq hne
    refine Nat.Coprime.prod_left (fun i hi => Nat.Coprime.pow 2 2 ?_)
    exact (Nat.coprime_primes (hpp i) hq).mpr (Ne.symm (hne i hi))
  -- Counting the excluded j < J.
  --
  set R := c + Q + k with hR
  have hR1 : 1 ≤ R := by omega
  set J := 10000 * R ^ 2 with hJ
  have hJ1 : 1 ≤ J := by
    have := Nat.one_le_pow 2 R hR1
    simp only [hJ]
    omega
  set S := Nat.sqrt (c + Q * J + k) with hS
  set bad := (range (S + 1)).filter (fun q => q.Prime ∧ ∀ i ∈ t, q ≠ p i) with hbad
  set A : ℕ → Finset ℕ := fun q => (range J).filter (fun j => q ^ 2 ∣ c + Q * j) with hA
  set B : ℕ → Finset ℕ := fun q => (range J).filter (fun j => q ^ 2 ∣ (c + k) + Q * j) with hB
  have hcardq : ∀ q ∈ bad, ((A q ∪ B q).card : ℝ) ≤ 2 * ((J : ℝ) / (q : ℝ) ^ 2 + 1) := by
    intro q hq
    simp only [hbad, mem_filter] at hq
    have hcq := hQcop q hq.2.1 hq.2.2
    have hq2 : 0 < q ^ 2 := pow_pos hq.2.1.pos 2
    have h1 := B16_7_class (q ^ 2) Q c J hcq
    have h2 := B16_7_class (q ^ 2) Q (c + k) J hcq
    have h3 := card_union_le (A q) (B q)
    have hdiv : ((J / q ^ 2 : ℕ) : ℝ) ≤ (J : ℝ) / (q : ℝ) ^ 2 := by
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.2.1.pos
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self J (q ^ 2)
    have : ((A q ∪ B q).card : ℝ) ≤ 2 * (((J / q ^ 2 : ℕ) : ℝ) + 1) := by
      have : (A q ∪ B q).card ≤ 2 * (J / q ^ 2 + 1) := by
        simp only [hA, hB] at h3 ⊢
        omega
      exact_mod_cast this
    linarith
  have hsumq : ∑ q ∈ bad, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 35 / 72 :=
    (sum_le_sum_of_subset_of_nonneg (fun q hq => by
        simp only [hbad, mem_filter] at hq ⊢
        exact ⟨hq.1, hq.2.1⟩)
      (fun _ _ _ => by positivity)).trans (B16_7_sum (S + 1))
  have hcardbad : (bad.card : ℝ) ≤ S + 1 := by
    have := card_le_card (filter_subset (fun q => q.Prime ∧ ∀ i ∈ t, q ≠ p i) (range (S + 1)))
    rw [card_range] at this
    exact_mod_cast this
  have hSle : 72 * (S + 1) < J := by
    have h1 : S * S ≤ c + Q * J + k := Nat.sqrt_le _
    have h2 : c + Q * J + k ≤ R * J := by
      simp only [hR]
      nlinarith
    have h3 : S * S ≤ (100 * R ^ 2) * (100 * R ^ 2) := by
      calc S * S ≤ R * J := h1.trans h2
        _ = 10000 * R ^ 3 := by rw [hJ]; ring
        _ ≤ 10000 * R ^ 4 := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right hR1 (by norm_num)
        _ = _ := by ring
    have h4 : S ≤ 100 * R ^ 2 := Nat.mul_self_le_mul_self_iff.mp h3
    have h5 : 1 ≤ R ^ 2 := Nat.one_le_pow _ _ hR1
    simp only [hJ]
    omega
  have hcount : (bad.biUnion (fun q => A q ∪ B q)).card < J := by
    have h1 := card_biUnion_le (s := bad) (t := fun q => A q ∪ B q)
    have h2 : (((bad.biUnion (fun q => A q ∪ B q)).card : ℕ) : ℝ) ≤
        ∑ q ∈ bad, 2 * ((J : ℝ) / (q : ℝ) ^ 2 + 1) :=
      (by exact_mod_cast h1 : _ ≤ (∑ q ∈ bad, ((A q ∪ B q).card : ℝ))).trans
        (sum_le_sum hcardq)
    have h3 : ∑ q ∈ bad, 2 * ((J : ℝ) / (q : ℝ) ^ 2 + 1) =
        2 * J * ∑ q ∈ bad, (1 : ℝ) / (q : ℝ) ^ 2 + 2 * bad.card := by
      rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun q _ => ?_)
      push_cast
      ring
    have h4 : ((72 * (S + 1) : ℕ) : ℝ) < J := by exact_mod_cast hSle
    push_cast at h4
    have hJ0 : (0 : ℝ) ≤ J := by positivity
    have h5 : 2 * (J : ℝ) * ∑ q ∈ bad, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 2 * (J : ℝ) * (35 / 72) :=
      mul_le_mul_of_nonneg_left hsumq (by positivity)
    have : (((bad.biUnion (fun q => A q ∪ B q)).card : ℕ) : ℝ) < J := by
      rw [h3] at h2
      linarith
    exact_mod_cast this
  obtain ⟨j, hjJ, hjgood⟩ : ∃ j ∈ range J, j ∉ bad.biUnion (fun q => A q ∪ B q) := by
    by_contra h
    push Not at h
    have := card_le_card (show range J ⊆ bad.biUnion (fun q => A q ∪ B q) from h)
    rw [card_range] at this
    omega
  rw [mem_range] at hjJ
  set m := c + Q * j with hm
  have h1t : 1 ∈ t := by simp [ht]; omega
  -- No q^2 with q prime outside {p_i} divides m or m + k.
  --
  have hfree : ∀ x, (x = m ∨ x = m + k) → Squarefree x := by
    intro x hx
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hqq
    rw [← pow_two] at hqq
    by_cases hP : ∃ i ∈ t, q = p i
    · obtain ⟨i, hi, rfl⟩ := hP
      have hr := hres i hi j
      have hit : 0 < i ∧ i < k := by simpa [ht] using hi
      have := hsq i
      rcases hx with rfl | rfl
      · rw [Nat.mod_eq_zero_of_dvd hqq] at hr
        omega
      · have h0 := Nat.mod_eq_zero_of_dvd hqq
        rw [Nat.add_mod, hr, Nat.mod_eq_of_lt (show k < p i ^ 2 by omega)] at h0
        have : (p i ^ 2 - i + k) % (p i ^ 2) = k - i := by
          rw [show p i ^ 2 - i + k = (k - i) + p i ^ 2 by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        omega
    · push Not at hP
      have hx0 : x ≠ 0 := by
        rcases hx with rfl | rfl
        · intro h0
          have := hres 1 h1t j
          rw [← hm, h0, Nat.zero_mod] at this
          have := hsq 1
          omega
        · omega
      have hle : q * q ≤ c + Q * J + k := by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hqq
        have hmJ : Q * j ≤ Q * J := Nat.mul_le_mul_left _ hjJ.le
        rcases hx with rfl | rfl <;> nlinarith
      have hqS : q < S + 1 := Nat.lt_succ_of_le (Nat.le_sqrt.mpr hle)
      apply hjgood
      rw [mem_biUnion]
      refine ⟨q, ?_, ?_⟩
      · simp only [hbad, mem_filter, mem_range]
        exact ⟨hqS, hq, fun i hi => hP i hi⟩
      · rcases hx with rfl | rfl
        · exact mem_union_left _ (by simp only [hA, mem_filter, mem_range]; exact ⟨hjJ, hqq⟩)
        · refine mem_union_right _ ?_
          simp only [hB, mem_filter, mem_range]
          exact ⟨hjJ, by rw [show c + k + Q * j = c + Q * j + k by ring]; exact hqq⟩
  refine ⟨m, hfree m (Or.inl rfl), hfree (m + k) (Or.inr rfl), fun i hi1 hi2 => ?_⟩
  have hi : i ∈ t := by simp [ht]; omega
  have hr := hres i hi j
  have := hsq i
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  refine ⟨p i, hpp i, ?_⟩
  rw [← pow_two]
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, hr, Nat.mod_eq_of_lt (show i < p i ^ 2 by omega),
    show p i ^ 2 - i + i = p i ^ 2 by omega, Nat.mod_self]

theorem B16_7_main (k : ℕ) (hk : 1 ≤ k) :
    ∃ n, Nat.nth Squarefree (n + 1) - Nat.nth Squarefree n = k := by
  obtain ⟨m, hm, hmk, hmid⟩ := B16_7_gap k hk
  refine ⟨Nat.count Squarefree m, ?_⟩
  have h1 : Nat.nth Squarefree (Nat.count Squarefree m) = m := Nat.nth_count hm
  have hc : Nat.count Squarefree (m + k) = Nat.count Squarefree m + 1 := by
    rw [Nat.count_add]
    congr 1
    rw [Nat.count_eq_card_filter_range]
    have : (range k).filter (fun i => Squarefree (m + i)) = {0} := by
      ext i
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_contra h0
        exact hmid i (Nat.pos_of_ne_zero h0) h1 h2
      · rintro rfl
        exact ⟨by omega, by simpa using hm⟩
    rw [this, card_singleton]
  have h2 : Nat.nth Squarefree (Nat.count Squarefree m + 1) = m + k := by
    rw [← hc]
    exact Nat.nth_count hmk
  rw [h1, h2]
  omega
