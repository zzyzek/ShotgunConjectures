/-
OEIS A008578 (1 and the primes), conjecture (I. Gerasimova 2013): the sequence
contains exactly those k with sigma(k) > k·BigOmega(k).

Main theorems.
* `A008578_conjecture`: for every k ≥ 1, (k = 1 ∨ k prime) ↔ k·Ω(k) < σ(k),
  with σ = `ArithmeticFunction.sigma 1` and Ω = `ArithmeticFunction.cardFactors`.
* `composite_sigma_le`: for composite k (k ≥ 2, not prime), σ(k) ≤ k·Ω(k),
  and equality forces k = 6.
Together these are the README result.

Proof.  With S = primeFactors k and f = factorization k, σ(k)/k is the
product over p ∈ S of σ(p^f(p))/p^f(p).  Adding primes in increasing order
(`Finset.induction_on_max`), the new prime P satisfies P ≥ |S_old| + 2, which
gives σ(k)/k < |S| + 1 for k ≥ 2 (`prod_lt_card_add_one`), and for squarefree k
σ(k)/k ≤ (|S| + 2)/2 (`prod_sqfree_le`).  Non-squarefree composites have
Ω ≥ |S| + 1; squarefree ones with |S| ≥ 3 have (|S|+2)/2 < |S| = Ω; for
k = pq, (p+1)(q+1) ≤ 2pq with equality only for {p, q} = {2, 3}.

Not checked: nothing outside Lean.
-/
import Mathlib

open ArithmeticFunction Finset

lemma sigma_prime_pow_rat {P e : ℕ} (hP : P.Prime) :
    ((sigma 1 (P ^ e) : ℕ) : ℚ) * ((P : ℚ) - 1) = (P : ℚ) * (P : ℚ) ^ e - 1 := by
  rw [sigma_one_apply_prime_pow hP]
  push_cast
  rw [geom_sum_mul]; ring

/-- σ(k)/k < ω(k) + 1 type bound, over an arbitrary finite set of primes. -/
lemma prod_lt_card_add_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) :
    0 < ∏ p ∈ S, ((sigma 1 (p ^ e p) : ℕ) : ℚ) / ((p : ℚ) ^ e p) ∧
    ∏ p ∈ S, ((sigma 1 (p ^ e p) : ℕ) : ℚ) / ((p : ℚ) ^ e p) ≤ S.card + 1 ∧
    (S.Nonempty → ∏ p ∈ S, ((sigma 1 (p ^ e p) : ℕ) : ℚ) / ((p : ℚ) ^ e p) < S.card + 1) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hS a (mem_insert_self a s)
    have ih := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have hnot : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [prod_insert hnot, card_insert_of_notMem hnot]
    obtain ⟨hA0, hA, _⟩ := ih
    set A := ∏ p ∈ s, ((sigma 1 (p ^ e p) : ℕ) : ℚ) / ((p : ℚ) ^ e p)
    set D : ℚ := (a : ℚ) ^ e a
    set σa : ℚ := ((sigma 1 (a ^ e a) : ℕ) : ℚ)
    have hD1 : 1 ≤ D := one_le_pow₀ (by exact_mod_cast ha.one_lt.le)
    have hP2 : (2 : ℚ) ≤ a := by exact_mod_cast ha.two_le
    have hσ := sigma_prime_pow_rat (e := e a) ha
    have hσD : D ≤ σa := by nlinarith
    have hD0 : 0 < D := by linarith
    set x := σa / D
    have hx1 : 1 ≤ x := by rw [le_div_iff₀ hD0]; linarith
    have hxP : (x - 1) * ((a : ℚ) - 1) < 1 := by
      have : (x - 1) * ((a : ℚ) - 1) = (D - 1) / D := by
        simp only [x]; field_simp; linear_combination hσ
      rw [this, div_lt_one hD0]; linarith
    -- s consists of primes below a, so |s| ≤ a - 2.
    have hcard : (s.card : ℚ) + 1 ≤ (a : ℚ) - 1 := by
      have hsub : s ⊆ Ico 2 a := by
        intro p hp
        simp only [mem_Ico]
        exact ⟨(hS p (mem_insert_of_mem hp)).two_le, hlt p hp⟩
      have := card_le_card hsub
      simp only [Nat.card_Ico] at this
      have h2 : 2 ≤ a := ha.two_le
      have : (s.card : ℚ) ≤ (a : ℚ) - 2 := by
        have : ((a - 2 : ℕ) : ℚ) = (a : ℚ) - 2 := by push_cast [Nat.cast_sub h2]; ring
        rw [← this]; exact_mod_cast ‹s.card ≤ a - 2›
      linarith
    have hx0 : 0 < x := by linarith
    have hmain : A * x < (s.card : ℚ) + 1 + 1 := by
      have h1 : A * x = A + A * (x - 1) := by ring
      have h2 : A * (x - 1) ≤ ((s.card : ℚ) + 1) * (x - 1) :=
        mul_le_mul_of_nonneg_right hA (by linarith)
      have h3 : ((s.card : ℚ) + 1) * (x - 1) ≤ ((a : ℚ) - 1) * (x - 1) :=
        mul_le_mul_of_nonneg_right hcard (by linarith)
      nlinarith
    push_cast
    refine ⟨mul_pos hx0 hA0, ?_, fun _ => ?_⟩
    · rw [mul_comm]; linarith
    · rw [mul_comm]; linarith

/-- For squarefree numbers: ∏ (1 + 1/p) ≤ (|S| + 2)/2. -/
lemma prod_sqfree_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, ((p : ℚ) + 1) / p ∧ ∏ p ∈ S, ((p : ℚ) + 1) / p ≤ ((S.card : ℚ) + 2) / 2 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hS a (mem_insert_self a s)
    have ih := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have hnot : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [prod_insert hnot, card_insert_of_notMem hnot]
    obtain ⟨hA0, hA⟩ := ih
    set A := ∏ p ∈ s, ((p : ℚ) + 1) / p
    have hcard : (s.card : ℚ) + 2 ≤ (a : ℚ) := by
      have hsub : s ⊆ Ico 2 a := by
        intro p hp
        simp only [mem_Ico]
        exact ⟨(hS p (mem_insert_of_mem hp)).two_le, hlt p hp⟩
      have := card_le_card hsub
      simp only [Nat.card_Ico] at this
      have h2 : 2 ≤ a := ha.two_le
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    have hP0 : (0 : ℚ) < a := by exact_mod_cast ha.pos
    refine ⟨mul_pos (by positivity) hA0, ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hP0 (by norm_num)]
    have : (A * 2) ≤ (s.card : ℚ) + 2 := (le_div_iff₀ (by norm_num : (0:ℚ) < 2)).1 hA
    nlinarith

lemma sigma_div_eq (n : ℕ) (hn : n ≠ 0) :
    ((sigma 1 n : ℕ) : ℚ) / n =
      ∏ p ∈ n.primeFactors, ((sigma 1 (p ^ n.factorization p) : ℕ) : ℚ) /
        ((p : ℚ) ^ n.factorization p) := by
  have h1 := IsMultiplicative.multiplicative_factorization (sigma 1) isMultiplicative_sigma hn
  have h2 := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at h1 h2
  rw [prod_div_distrib]
  congr 1
  · rw [h1]; push_cast; rfl
  · conv_lhs => rw [← h2]
    push_cast; rfl

lemma omega_eq (n : ℕ) : cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
  rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]

theorem composite_sigma_le (k : ℕ) (h2 : 2 ≤ k) (hnp : ¬ k.Prime) :
    sigma 1 k ≤ k * cardFactors k ∧ (sigma 1 k = k * cardFactors k → k = 6) := by
  have hk0 : k ≠ 0 := by omega
  set S := k.primeFactors
  set f := k.factorization
  have hpr : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hf1 : ∀ p ∈ S, 1 ≤ f p := fun p hp =>
    (Nat.Prime.factorization_pos_of_dvd (hpr p hp) hk0 (Nat.dvd_of_mem_primeFactors hp))
  have hSne : S.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hr := sigma_div_eq k hk0
  have hΩ := omega_eq k
  have hk0q : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  -- It suffices to show σ(k)/k < Ω(k) (strict), or handle k = pq.
  have strict : ((sigma 1 k : ℕ) : ℚ) / k < cardFactors k →
      sigma 1 k ≤ k * cardFactors k ∧ (sigma 1 k = k * cardFactors k → k = 6) := by
    intro h
    rw [div_lt_iff₀ hk0q] at h
    have : sigma 1 k < cardFactors k * k := by exact_mod_cast h
    constructor
    · rw [mul_comm]; omega
    · intro heq; rw [mul_comm] at heq; omega
  by_cases hsq : ∃ p ∈ S, 2 ≤ f p
  · -- Not squarefree: Ω ≥ |S| + 1 > σ/k.
    obtain ⟨p, hp, hp2⟩ := hsq
    apply strict
    obtain ⟨_, _, hlt⟩ := prod_lt_card_add_one S hpr f
    rw [hr]
    refine lt_of_lt_of_le (hlt hSne) ?_
    have : S.card + 1 ≤ cardFactors k := by
      rw [hΩ]
      have hsplit : ∑ q ∈ S, f q = ∑ q ∈ S, 1 + ∑ q ∈ S, (f q - 1) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro q hq; have := hf1 q hq; omega
      have : f p - 1 ≤ ∑ q ∈ S, (f q - 1) :=
        single_le_sum (f := fun q => f q - 1) (fun _ _ => Nat.zero_le _) hp
      rw [hsplit, card_eq_sum_ones]; omega
    exact_mod_cast this
  · push Not at hsq
    have hfe : ∀ p ∈ S, f p = 1 := fun p hp => by have := hf1 p hp; have := hsq p hp; omega
    have hΩS : cardFactors k = S.card := by
      rw [hΩ, card_eq_sum_ones]; exact sum_congr rfl hfe
    have hrS : ((sigma 1 k : ℕ) : ℚ) / k = ∏ p ∈ S, ((p : ℚ) + 1) / p := by
      rw [hr]
      apply prod_congr rfl
      intro p hp
      have e := sigma_one_apply_prime_pow (i := 1) (hpr p hp)
      rw [pow_one] at e
      rw [hfe p hp, pow_one, pow_one, e]
      simp [sum_range_succ]; ring
    have hkS : k = ∏ p ∈ S, p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk0]
      rw [Finsupp.prod, Nat.support_factorization]
      exact prod_congr rfl (fun p hp => by rw [hfe p hp, pow_one])
    have hc2 : 2 ≤ S.card := by
      by_contra hc
      have : S.card = 1 := by
        have := hSne.card_pos; omega
      obtain ⟨p, hpS⟩ := card_eq_one.mp this
      rw [hpS, prod_singleton] at hkS
      exact hnp (hkS ▸ hpr p (by rw [hpS]; exact mem_singleton_self p))
    rcases Nat.lt_or_ge 2 S.card with h3 | h3
    · apply strict
      rw [hrS, hΩS]
      have := (prod_sqfree_le S hpr).2
      have h3' : (3 : ℚ) ≤ S.card := by exact_mod_cast h3
      linarith
    · have hcard : S.card = 2 := by omega
      obtain ⟨p, q, hpq, hS2⟩ := card_eq_two.mp hcard
      have hp : p.Prime := hpr p (by rw [hS2]; simp)
      have hq : q.Prime := hpr q (by rw [hS2]; simp)
      have hk : k = p * q := by rw [hkS, hS2, prod_pair hpq]
      have hσ : sigma 1 k = (p + 1) * (q + 1) := by
        rw [hk, isMultiplicative_sigma.map_mul_of_coprime
          ((Nat.coprime_primes hp hq).2 hpq)]
        have e1 := sigma_one_apply_prime_pow (i := 1) hp
        have e2 := sigma_one_apply_prime_pow (i := 1) hq
        simp only [pow_one] at e1 e2
        rw [e1, e2]; simp [sum_range_succ]; ring
      rw [hΩS, hcard, hσ, hk]
      have hp2 := hp.two_le
      have hq2 := hq.two_le
      constructor
      · rcases Nat.lt_or_gt_of_ne hpq with h | h <;> nlinarith
      · intro heq
        rcases Nat.lt_or_gt_of_ne hpq with h | h
        · have : p = 2 := by
            by_contra hne
            have : 3 ≤ p := by omega
            nlinarith
          subst this
          have : q = 3 := by nlinarith
          subst this; rfl
        · have : q = 2 := by
            by_contra hne
            have : 3 ≤ q := by omega
            nlinarith
          subst this
          have : p = 3 := by nlinarith
          subst this; rfl

theorem A008578_conjecture (k : ℕ) (hk : 1 ≤ k) :
    (k = 1 ∨ k.Prime) ↔ k * cardFactors k < sigma 1 k := by
  constructor
  · rintro (rfl | hp)
    · simp
    · have e := sigma_one_apply_prime_pow (i := 1) hp
      rw [pow_one] at e
      rw [cardFactors_apply_prime hp, e]
      simp [sum_range_succ]
  · intro h
    by_contra hc
    push Not at hc
    have := (composite_sigma_le k (by omega) hc.2).1
    omega
