/-
OEIS A219431: logarithmic derivative of the g.f. of A219430, where
A219430(n) = number of overpartitions of n^2 (A015128(n^2)).
Conjecture (entry comment): a(2n+1) ≡ 2 (mod 4), a(2n) ≡ 0 (mod 4).

Definitions.
* `overpart m` = Σ over partitions λ of m of 2^(number of distinct part
  sizes of λ): an overpartition is a partition in which the first occurrence
  of each part size may be overlined, so this is the overpartition count
  A015128(m).
* `A219430 n = overpart (n^2)`, with g.f. G(x) = Σ A219430(n) x^n (G(0) = 1).
* "a is the logarithmic derivative of G" means Σ a(n) x^n = x G'(x)/G(x),
  i.e. G(x) · Σ_{n≥1} a(n) x^n = x G'(x); coefficientwise
  Σ_{k=1}^{n} a(k) A219430(n-k) = n A219430(n) for n ≥ 1 (hypothesis `hlog`
  of `A219431_main`; it determines a uniquely since A219430(0) = 1).

Proof.
1. `overpart_mod4`: 2^c ≡ 0 (mod 4) for c ≥ 2, so overpart m ≡ 2·#{λ with one
   part size} (mod 4) for m ≥ 1, and partitions of m with a single part size
   s correspond to divisors s of m.  So overpart m ≡ 2 τ(m) (mod 4).
2. τ(n^2) = Π (2 e_p + 1) is odd, so A219430(n) ≡ 2 (mod 4) for n ≥ 1.
3. `logderiv_mod4`: if b(0) = 1, b(j) ≡ 2 (mod 4) for j ≥ 1 and
   Σ_{k=1}^{n} a(k) b(n-k) = n b(n), then by strong induction every a(k) is
   even, the products a(k) b(n-k) (k < n) are ≡ 0 (mod 4), and
   a(n) ≡ n b(n) ≡ 2n (mod 4).

Main theorem `A219431_main`.  Nothing outside this file except reading
"overpartition" and "logarithmic derivative" as above.
-/
import Mathlib

open Finset

/-- Number of overpartitions of m (A015128). -/
def overpart (m : ℕ) : ℕ := ∑ l : m.Partition, 2 ^ l.parts.toFinset.card

/-- A219430: overpartitions of n^2. -/
def A219430 (n : ℕ) : ℕ := overpart (n ^ 2)

theorem pow_two_mod4 (c : ℕ) (hc : 1 ≤ c) : 2 ^ c % 4 = if c = 1 then 2 else 0 := by
  rcases Nat.lt_or_ge c 2 with h | h
  · have : c = 1 := by omega
    subst this; rfl
  · simp only [show ¬ (c = 1) by omega, ↓reduceIte]
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
    rw [pow_add]; simp

theorem parts_card_pos {m : ℕ} (hm : 0 < m) (l : m.Partition) : 1 ≤ l.parts.toFinset.card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Multiset.toFinset_eq_empty]
  intro h
  have := l.parts_sum
  rw [h] at this
  simp at this
  omega

/-- Partitions with a single part size are counted by the divisors. -/
theorem card_single (m : ℕ) (hm : 0 < m) :
    (univ.filter (fun l : m.Partition => l.parts.toFinset.card = 1)).card = m.divisors.card := by
  classical
  refine Finset.card_bij (fun l _ => l.parts.toFinset.sum id) ?_ ?_ ?_
  · intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨s, hs⟩ := Finset.card_eq_one.1 hl.2
    rw [hs, Finset.sum_singleton, id, Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    have hrep : l.parts = Multiset.replicate (Multiset.card l.parts) s := by
      apply Multiset.eq_replicate_card.2
      intro b hb
      have : b ∈ l.parts.toFinset := Multiset.mem_toFinset.2 hb
      rw [hs] at this
      simpa using this
    have := l.parts_sum
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at this
    exact ⟨Multiset.card l.parts, by rw [mul_comm]; exact this.symm⟩
  · intro l1 hl1 l2 hl2 heq
    rw [Finset.mem_filter] at hl1 hl2
    obtain ⟨s1, hs1⟩ := Finset.card_eq_one.1 hl1.2
    obtain ⟨s2, hs2⟩ := Finset.card_eq_one.1 hl2.2
    simp only [hs1, hs2, Finset.sum_singleton, id] at heq
    subst heq
    have rep : ∀ l : m.Partition, l.parts.toFinset = {s1} →
        l.parts = Multiset.replicate (m / s1) s1 := by
      intro l hs
      have hrep : l.parts = Multiset.replicate (Multiset.card l.parts) s1 := by
        apply Multiset.eq_replicate_card.2
        intro b hb
        have : b ∈ l.parts.toFinset := Multiset.mem_toFinset.2 hb
        rw [hs] at this
        simpa using this
      have hsum := l.parts_sum
      rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
      have hpos : 0 < s1 := l.parts_pos (Multiset.mem_toFinset.1 (by rw [hs]; simp))
      rw [hrep]
      congr 1
      exact (Nat.div_eq_of_eq_mul_left hpos hsum.symm).symm
    have e1 := rep l1 hs1
    have e2 := rep l2 hs2
    cases l1; cases l2
    simp only at e1 e2
    subst e1; subst e2
    rfl
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨r, hr⟩, -⟩ := hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hr; omega
      · exact h
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at hr; omega
      · exact h
    let l : m.Partition :=
      { parts := Multiset.replicate r d
        parts_pos := by
          intro i hi
          rw [Multiset.eq_of_mem_replicate hi]; exact hd0
        parts_sum := by rw [Multiset.sum_replicate, smul_eq_mul, hr, mul_comm] }
    have hts : l.parts.toFinset = {d} := by
      show (Multiset.replicate r d).toFinset = {d}
      rw [Multiset.toFinset_replicate]; simp only [show ¬ (r = 0) by omega, ↓reduceIte]
    refine ⟨l, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hts]; rfl⟩
    · rw [hts]; simp

theorem overpart_mod4 (m : ℕ) (hm : 0 < m) : overpart m % 4 = 2 * m.divisors.card % 4 := by
  classical
  unfold overpart
  rw [Finset.sum_nat_mod]
  have : ∀ l : m.Partition, 2 ^ l.parts.toFinset.card % 4
      = if l.parts.toFinset.card = 1 then 2 else 0 :=
    fun l => pow_two_mod4 _ (parts_card_pos hm l)
  simp_rw [this]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    card_single m hm, mul_comm]

theorem divisors_sq_odd (n : ℕ) (hn : 0 < n) : (n ^ 2).divisors.card % 2 = 1 := by
  rw [Nat.card_divisors (by positivity), ← Nat.odd_iff]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro p _
  rw [Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  exact ⟨n.factorization p, by ring⟩

theorem A219430_mod4 (n : ℕ) (hn : 0 < n) : A219430 n % 4 = 2 := by
  unfold A219430
  rw [overpart_mod4 _ (by positivity)]
  have := divisors_sq_odd n hn
  omega

theorem A219430_zero : A219430 0 = 1 := by
  unfold A219430 overpart
  simp

/-- The logarithmic-derivative step. -/
theorem logderiv_mod4 (b a : ℕ → ℤ) (hb : ∀ j, 1 ≤ j → b j % 4 = 2) (hb0 : b 0 = 1)
    (hlog : ∀ n, 1 ≤ n → ∑ k ∈ Icc 1 n, a k * b (n - k) = n * b n) :
    ∀ n, 1 ≤ n → a n % 4 = if n % 2 = 1 then 2 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hsplit := hlog n hn
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hn, Nat.sub_self, hb0, mul_one] at hsplit
    have hdvd : (4 : ℤ) ∣ ∑ k ∈ Ico 1 n, a k * b (n - k) := by
      apply Finset.dvd_sum
      intro k hk
      rw [Finset.mem_Ico] at hk
      have h1 := ih k hk.2 hk.1
      have h2 := hb (n - k) (by omega)
      have ha : (2 : ℤ) ∣ a k := by
        split_ifs at h1 <;> omega
      have hb2 : (2 : ℤ) ∣ b (n - k) := by omega
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb2
      exact ⟨u * v, by rw [hu, hv]; ring⟩
    obtain ⟨q, hq⟩ : ∃ q, b n = 4 * q + 2 := ⟨b n / 4, by have := hb n hn; omega⟩
    have hnb : (n : ℤ) * b n = 4 * ((n : ℤ) * q) + 2 * n := by rw [hq]; ring
    obtain ⟨t, ht⟩ := hdvd
    have han : a n = 4 * ((n : ℤ) * q) + 2 * n - 4 * t := by linarith
    rw [han]
    split_ifs with hodd <;> omega

/-- Main theorem: if a is the logarithmic derivative of G(x) = Σ A219430(n) x^n,
i.e. G · Σ_{n ≥ 1} a(n) x^n = x G', then a(2n+1) ≡ 2 and a(2n) ≡ 0 (mod 4)
(n ≥ 1 for the even case). -/
theorem A219431_main (a : ℕ → ℤ)
    (hlog : ∀ n, 1 ≤ n → ∑ k ∈ Icc 1 n, a k * (A219430 (n - k) : ℤ) = n * (A219430 n : ℤ)) :
    (∀ n, a (2 * n + 1) % 4 = 2) ∧ (∀ n, 1 ≤ n → a (2 * n) % 4 = 0) := by
  have key := logderiv_mod4 (fun j => (A219430 j : ℤ)) a
    (fun j hj => by have := A219430_mod4 j hj; omega)
    (by simp [A219430_zero]) hlog
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · have := key (2 * n + 1) (by omega)
    simp only [show (2 * n + 1) % 2 = 1 by omega, ↓reduceIte] at this; exact this
  · have := key (2 * n) (by omega)
    simp only [show ¬ ((2 * n) % 2 = 1) by omega, ↓reduceIte] at this; exact this
