import Mathlib

/-
OEIS A054656: a(n) = number of primes p <= n that occur in no partition of n
into distinct primes.
Conjecture (entry): for n >= 23, a(n) = 2 if n-6 and n-4 are both prime,
a(n) = 1 if one of n-6, n-4, n-1 is prime, and a(n) = 0 otherwise.

Definitions.  `IsPart n s`: the finite set `s` consists of primes and sums to
`n` (a partition of n into distinct primes).  `a n` counts the primes
`p <= n` with no `s` such that `IsPart n s` and `p ∈ s`.

Main theorem.
* `A054656_formula`: for every n >= 23, `a n` equals the conjectured value.

Route.
* `G_of_ge`: for x >= 6 and any prime p, the interval (x, 2x] contains a
  prime other than p (two primes in (x, 2x]).  For x >= 512 this is
  `G_large`, the Erdős proof of Bertrand's postulate with one extra factor
  2x (`centralBinom_le_of_one_prime`, `real_ineq`, `main_ineq`, adapted from
  Mathlib's `Mathlib/NumberTheory/Bertrand.lean`); for 6 <= x < 512 a chain
  of primes (`G_step`).
* `rep_large`: Richert-type induction.  Every m > 27 is a sum of distinct
  primes, none equal to p, all below any bound r >= 31 with m <= 27 + r.
  Base m <= 87 from the table `tab`; step: subtract a prime q != p in
  ((m-28)/2, m-28].
* `rep_avoid`: every m other than 1, 4, 6 is a sum of distinct primes
  avoiding p, unless (m, p) is one of the nine pairs in `excL`, all with
  m + p <= 22.
* `no_rep_146`: 1, 4, 6 are not sums of distinct primes.
* `appears_iff`: for n >= 23, a prime p <= n is in some partition of n iff
  n - p is not 1, 4 or 6.

Not checked in this file: agreement of `a` with the OEIS data terms
(certificate/check.py computes a(0..3000) from the same definition).
-/

namespace A054656

open Finset

/-- A partition of `n` into distinct primes. -/
def IsPart (n : ℕ) (s : Finset ℕ) : Prop := (∀ x ∈ s, x.Prime) ∧ ∑ x ∈ s, x = n

/-- OEIS A054656. -/
noncomputable def a (n : ℕ) : ℕ :=
  by classical exact
    ((range (n + 1)).filter (fun p => p.Prime ∧ ¬ ∃ s, IsPart n s ∧ p ∈ s)).card

/-! ## Two primes in (x, 2x] -/

/-- `(x, 2x]` contains a prime different from any given `p`. -/
def G (x : ℕ) : Prop := ∀ p, ∃ q, q.Prime ∧ q ≠ p ∧ x < q ∧ q ≤ 2 * x

section RealPart

open Real

theorem real_ineq {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * (2 * x) * (2 * x) ^ √(2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + log x + log 2 + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos (mul_pos h (mul_pos two_pos h)) (rpow_pos_of_pos (mul_pos two_pos h) _))
      (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos (mul_pos h5 h6) h7).ne' (rpow_pos_of_pos four_pos _).ne',
      log_mul (mul_pos h5 h6).ne' h7.ne', log_mul h5.ne' h6.ne', log_mul two_ne_zero h5.ne',
      log_rpow h6, log_rpow zero_lt_four]
    simp only [f]
    rw [log_mul two_ne_zero h5.ne']
    ring
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · apply ConcaveOn.add
        · apply ConcaveOn.add
          · exact strictConcaveOn_log_Ioi.concaveOn.subset
              (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
          · exact strictConcaveOn_log_Ioi.concaveOn.subset
              (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
        · exact concaveOn_const _ (convex_Ioi 0.5)
      convert!
        ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : ℝ) • LinearMap.id)))
        using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_right₀ (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : ℝ) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonneg_iff (by positivity), this, one_le_div (by norm_num1)]
    have e1 : ((2 : ℝ) * 18) ^ (6 : ℝ) = ((2 : ℝ) * 18) ^ (6 : ℕ) := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : (4 : ℝ) ^ ((18 : ℝ) / 3) = (4 : ℝ) ^ (6 : ℕ) := by
      rw [show (18 : ℝ) / 3 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2]
    norm_num
  · have hs : √(2 * 512 : ℝ) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonpos_iff (hf' _ (by norm_num1)).le, hs,
      div_le_one (by positivity)]
    have e1 : ((2 : ℝ) * 512) ^ (32 : ℝ) = ((2 : ℝ) * 512) ^ (32 : ℕ) := by
      rw [show (32 : ℝ) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : (4 : ℝ) ^ (170 : ℕ) ≤ (4 : ℝ) ^ ((512 : ℝ) / 3) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [e1]
    refine le_trans ?_ e2
    norm_num

end RealPart

section NatPart

open Nat

theorem main_ineq {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) * (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  rw [← @Nat.cast_le ℝ]
  simp only [Nat.cast_mul, Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_ofNat]
  refine _root_.trans ?_ (real_ineq (by exact_mod_cast n_large))
  gcongr
  · have n2_pos : 0 < 2 * n := by positivity
    exact mod_cast n2_pos
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact Nat.cast_div_le.trans (by norm_cast)

/-- The central binomial coefficient when `(n, 2n]` holds at most one prime `q`. -/
theorem centralBinom_le_of_one_prime (n q : ℕ) (n_large : 2 < n)
    (one : ∀ p : ℕ, p.Prime → n < p → p ≤ 2 * n → p = q) :
    centralBinom n ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) := by
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let f x := x ^ n.centralBinom.factorization x
  have hsub : range (2 * n / 3 + 1) ⊆ range (2 * n + 1) := by
    intro x hx; simp only [mem_range] at hx ⊢; omega
  have hsplit : (∏ x ∈ range (2 * n + 1) \ range (2 * n / 3 + 1), f x) *
      ∏ x ∈ range (2 * n / 3 + 1), f x = centralBinom n := by
    rw [Finset.prod_sdiff hsub]
    exact Nat.prod_pow_factorization_centralBinom n
  have hrest : ∏ x ∈ range (2 * n + 1) \ range (2 * n / 3 + 1), f x ≤ 2 * n := by
    have hone : ∀ x ∈ range (2 * n + 1) \ range (2 * n / 3 + 1), x ≠ q → f x = 1 := by
      intro x hx hxq
      simp only [mem_sdiff, mem_range] at hx
      dsimp only [f]
      by_cases hp : x.Prime
      · by_cases hxn : x ≤ n
        · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hxn (by omega),
            Nat.pow_zero]
        · exact absurd (one x hp (by omega) (by omega)) hxq
      · rw [factorization_eq_zero_of_not_prime _ hp, Nat.pow_zero]
    by_cases hq : q ∈ range (2 * n + 1) \ range (2 * n / 3 + 1)
    · rw [Finset.prod_eq_single_of_mem q hq (fun x hx hxq => hone x hx hxq)]
      exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    · rw [Finset.prod_eq_one (fun x hx => hone x hx (fun h => hq (h ▸ hx)))]
      exact n2_pos
  have hsmall : ∏ x ∈ range (2 * n / 3 + 1), f x ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose h; dsimp only [f]
      rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
    rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : #(Finset.Icc 1 (Nat.sqrt (2 * n))) = Nat.sqrt (2 * n) := by
        rw [card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  rw [← hsplit, mul_comm (∏ x ∈ range (2 * n + 1) \ range (2 * n / 3 + 1), f x)]
  exact Nat.mul_le_mul hsmall hrest

theorem G_large (n : ℕ) (hn : 512 ≤ n) : G n := by
  intro p
  by_contra hne
  push Not at hne
  have one : ∀ r, r.Prime → n < r → r ≤ 2 * n → r = p := by
    intro r hr h1 h2
    by_contra h
    exact absurd h2 (not_le.2 (hne r hr h h1))
  have h1 := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le_of_one_prime n p (by omega) one
  have h3 := main_ineq hn
  have : n * centralBinom n ≤ 4 ^ n :=
    calc n * centralBinom n
        ≤ n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n)) :=
          Nat.mul_le_mul_left _ h2
      _ = n * (2 * n) * (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by ring
      _ ≤ 4 ^ n := h3
  omega

theorem G_step {n : ℕ} (q1 q2 r : ℕ) (h1 : q1.Prime) (h2 : q2.Prime) (hlt : q2 < q1)
    (cov : q1 ≤ 2 * r) (H : n < r → G n) (hn : n < q2) : G n := by
  by_cases hr : n < r
  · exact H hr
  intro p
  by_cases hp : q1 = p
  · exact ⟨q2, h2, by omega, hn, by omega⟩
  · exact ⟨q1, h1, hp, by omega, by omega⟩

/-- Two primes in `(x, 2x]` for every `x ≥ 6`. -/
theorem G_of_ge (n : ℕ) (hn : 6 ≤ n) : G n := by
  rcases le_or_gt 512 n with h | h
  · exact G_large n h
  have h' : n < 521 := by omega
  refine G_step 523 521 269 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 521 269 263 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 269 263 139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 263 139 137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 139 137 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 137 73 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 73 71 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 71 41 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 41 37 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 37 29 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 29 23 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 23 19 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 19 17 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 17 13 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h'
  refine G_step 13 11 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h'
  intro h' p
  have hn6 : n = 6 := by omega
  subst hn6
  by_cases hp : p = 7
  · exact ⟨11, by norm_num, by omega, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, fun h => hp h.symm, by norm_num, by norm_num⟩

end NatPart

/-! ## Sums of distinct primes avoiding one prime -/

/-- Primes below 60 (every part used in `tab`). -/
def primesL : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

theorem prime_of_mem_primesL {x : ℕ} (hx : x ∈ primesL) : x.Prime := by
  simp only [primesL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> norm_num

/-- For `m ≤ 87`: representations of `m` as sums of distinct primes (empty for 1, 4, 6). -/
def tab : List (List (List ℕ)) :=
  [[[]], [], [[2]], [[3]], [], [[5], [2, 3]], [], [[7], [2, 5]], [[3, 5]], [[2, 7]],
   [[3, 7], [2, 3, 5]], [[11]], [[5, 7], [2, 3, 7]], [[13], [2, 11]], [[3, 11], [2, 5, 7]],
   [[2, 13], [3, 5, 7]], [[3, 13], [5, 11]], [[17], [2, 3, 5, 7]], [[5, 13], [7, 11]],
   [[19], [2, 17]], [[3, 17], [7, 13]], [[2, 19], [3, 5, 13]], [[3, 19], [5, 17]],
   [[23], [3, 7, 13]], [[5, 19], [7, 17]], [[2, 23], [3, 5, 17]], [[3, 23], [7, 19]],
   [[3, 5, 19], [3, 7, 17], [2, 5, 7, 13]], [[5, 23], [11, 17]], [[29], [3, 7, 19]],
   [[7, 23], [11, 19]], [[2, 29], [3, 5, 23]], [[3, 29], [13, 19]], [[3, 7, 23], [5, 11, 17]],
   [[5, 29], [11, 23]], [[5, 7, 23], [3, 13, 19]], [[7, 29], [13, 23]],
   [[3, 5, 29], [7, 11, 19]], [[2, 7, 29], [3, 5, 11, 19]], [[3, 7, 29], [5, 11, 23]],
   [[11, 29], [17, 23]], [[5, 7, 29], [11, 13, 17]], [[13, 29], [19, 23]],
   [[3, 11, 29], [7, 13, 23]], [[2, 13, 29], [3, 7, 11, 23]], [[3, 13, 29], [5, 17, 23]],
   [[17, 29], [3, 7, 13, 23]], [[5, 13, 29], [7, 17, 23]], [[19, 29], [3, 5, 17, 23]],
   [[3, 17, 29], [7, 19, 23]], [[2, 19, 29], [3, 7, 17, 23]], [[3, 19, 29], [11, 17, 23]],
   [[23, 29], [3, 13, 17, 19]], [[5, 19, 29], [13, 17, 23]], [[2, 23, 29], [5, 13, 17, 19]],
   [[3, 23, 29], [5, 7, 11, 13, 19]], [[3, 5, 19, 29], [2, 7, 11, 13, 23]],
   [[5, 23, 29], [3, 7, 11, 17, 19]], [[3, 7, 19, 29], [5, 13, 17, 23]],
   [[5, 23, 31], [11, 19, 29]], [[29, 31], [5, 13, 19, 23]], [[7, 23, 31], [13, 19, 29]],
   [[2, 29, 31], [3, 17, 19, 23]], [[3, 29, 31], [5, 7, 11, 17, 23]],
   [[3, 7, 23, 31], [5, 11, 19, 29]], [[5, 23, 37], [17, 19, 29]], [[29, 37], [5, 7, 23, 31]],
   [[7, 23, 37], [17, 19, 31]], [[31, 37], [3, 13, 23, 29]], [[5, 23, 41], [3, 29, 37]],
   [[29, 41], [2, 31, 37]], [[5, 23, 43], [11, 19, 41]], [[29, 43], [31, 41]],
   [[7, 23, 43], [3, 29, 41]], [[31, 43], [3, 7, 23, 41]], [[5, 23, 47], [3, 29, 43]],
   [[29, 47], [2, 31, 43]], [[7, 23, 47], [3, 31, 43]], [[31, 47], [37, 41]],
   [[3, 29, 47], [5, 31, 43]], [[37, 43], [2, 31, 47]], [[5, 23, 53], [3, 31, 47]],
   [[29, 53], [2, 37, 43]], [[7, 23, 53], [5, 31, 47]], [[31, 53], [37, 47]],
   [[3, 29, 53], [7, 31, 47]], [[2, 31, 53], [3, 7, 29, 47]], [[5, 23, 59], [3, 31, 53]]]

/-- The pairs `(m, p)` with `m ∉ {1, 4, 6}` and no sum of distinct primes equal to `m`
avoiding `p`. -/
def excL : List (ℕ × ℕ) :=
  [(2, 2), (3, 3), (8, 3), (8, 5), (9, 2), (9, 7), (10, 3), (11, 11), (12, 7)]

theorem excL_small : ∀ e ∈ excL, e.1 + e.2 ≤ 22 := by decide

theorem tab_ok : ∀ m, m < 88 → ∀ l ∈ tab.getD m [],
    l.sum = m ∧ l.Nodup ∧ ∀ x ∈ l, x ∈ primesL := by decide

theorem tab_ne : ∀ m, m < 88 → m ≠ 1 → m ≠ 4 → m ≠ 6 → tab.getD m [] ≠ [] := by decide

theorem tab_cover : ∀ m, m < 88 → ∀ x ∈ (tab.getD m []).headD [],
    (m, x) ∈ excL ∨ ∃ l ∈ tab.getD m [], x ∉ l := by decide

theorem tab_exc : ∀ e ∈ excL, e.1 ≤ 27 := by decide

theorem tab_bound : ∀ m, m < 88 → 27 < m → ∀ l ∈ tab.getD m [], ∀ x ∈ l,
    x < 31 ∨ x + 27 < m := by decide

/-- A table entry avoiding `p`. -/
theorem tab_avoid (m p : ℕ) (hm : m < 88) (h1 : m ≠ 1) (h4 : m ≠ 4) (h6 : m ≠ 6)
    (hex : (m, p) ∉ excL) : ∃ l ∈ tab.getD m [], p ∉ l := by
  obtain ⟨h, t, ht⟩ := List.exists_cons_of_ne_nil (tab_ne m hm h1 h4 h6)
  by_cases hp : p ∈ h
  · have := tab_cover m hm p (by rw [ht]; exact hp)
    tauto
  · exact ⟨h, by rw [ht]; exact List.mem_cons_self, hp⟩

theorem finset_of_list {l : List ℕ} (hnd : l.Nodup) : ∑ x ∈ l.toFinset, x = l.sum := by
  rw [List.sum_toFinset _ hnd, List.map_id']

/-- `Rep p r m`: `m` is a sum of distinct primes, none equal to `p`, all below `r`. -/
def Rep (p r m : ℕ) : Prop := ∃ s : Finset ℕ, (∀ x ∈ s, x.Prime ∧ x ≠ p ∧ x < r) ∧ ∑ x ∈ s, x = m

/-- Richert-type induction. -/
theorem rep_large (p : ℕ) : ∀ m, 27 < m → ∀ r, 31 ≤ r → m ≤ 27 + r → Rep p r m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm r hr31 hmr
  rcases lt_or_ge m 88 with hsm | hbig
  · have hex : (m, p) ∉ excL := fun h => by have := tab_exc _ h; simp at this; omega
    obtain ⟨l, hl, hpl⟩ := tab_avoid m p hsm (by omega) (by omega) (by omega) hex
    obtain ⟨hsum, hnd, hpr⟩ := tab_ok m hsm l hl
    refine ⟨l.toFinset, ?_, by rw [finset_of_list hnd, hsum]⟩
    intro x hx
    rw [List.mem_toFinset] at hx
    have hb := tab_bound m hsm hm l hl x hx
    exact ⟨prime_of_mem_primesL (hpr x hx), fun h => hpl (h ▸ hx), by omega⟩
  · obtain ⟨q, hq, hqp, hxq, hq2⟩ := G_of_ge ((m - 28) / 2) (by omega) p
    obtain ⟨s, hs, hsum⟩ := ih (m - q) (by omega) (by omega) q (by omega) (by omega)
    have hqs : q ∉ s := fun h => by have := (hs q h).2.2; omega
    refine ⟨insert q s, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ⟨hq, hqp, by omega⟩
      · obtain ⟨h1, h2, h3⟩ := hs y hy
        exact ⟨h1, h2, by omega⟩
    · rw [Finset.sum_insert hqs, hsum]
      omega

/-- Every `m ∉ {1, 4, 6}` is a sum of distinct primes avoiding `p`, unless `(m, p) ∈ excL`. -/
theorem rep_avoid (m p : ℕ) (h1 : m ≠ 1) (h4 : m ≠ 4) (h6 : m ≠ 6) (hex : (m, p) ∉ excL) :
    ∃ s : Finset ℕ, (∀ x ∈ s, x.Prime ∧ x ≠ p) ∧ ∑ x ∈ s, x = m := by
  rcases le_or_gt m 27 with hm | hm
  · obtain ⟨l, hl, hpl⟩ := tab_avoid m p (by omega) h1 h4 h6 hex
    obtain ⟨hsum, hnd, hpr⟩ := tab_ok m (by omega) l hl
    refine ⟨l.toFinset, ?_, by rw [finset_of_list hnd, hsum]⟩
    intro x hx
    rw [List.mem_toFinset] at hx
    exact ⟨prime_of_mem_primesL (hpr x hx), fun h => hpl (h ▸ hx)⟩
  · obtain ⟨s, hs, hsum⟩ := rep_large p m hm (m + 31) (by omega) (by omega)
    exact ⟨s, fun x hx => ⟨(hs x hx).1, (hs x hx).2.1⟩, hsum⟩

/-- 1, 4 and 6 are not sums of distinct primes. -/
theorem no_rep_146 (s : Finset ℕ) (hs : ∀ x ∈ s, x.Prime)
    (h : ∑ x ∈ s, x = 1 ∨ ∑ x ∈ s, x = 4 ∨ ∑ x ∈ s, x = 6) : False := by
  have hle : ∑ x ∈ s, x ≤ 6 := by omega
  have hsub : s ⊆ {2, 3, 5} := by
    intro x hx
    have hx6 : x ≤ 6 := le_trans (Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hx) hle
    have hp := hs x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases x <;> revert hp <;> norm_num
  have key : ∀ t ∈ ({2, 3, 5} : Finset ℕ).powerset,
      ∑ x ∈ t, x ≠ 1 ∧ ∑ x ∈ t, x ≠ 4 ∧ ∑ x ∈ t, x ≠ 6 := by decide
  have := key s (Finset.mem_powerset.2 hsub)
  omega

/-- For `n ≥ 23`, a prime `p ≤ n` is a part of some partition of `n` into distinct primes
iff `n - p ∉ {1, 4, 6}`. -/
theorem appears_iff {n p : ℕ} (hn : 23 ≤ n) (hp : p.Prime) (hpn : p ≤ n) :
    (∃ s, IsPart n s ∧ p ∈ s) ↔ ¬ (n - p = 1 ∨ n - p = 4 ∨ n - p = 6) := by
  constructor
  · rintro ⟨s, ⟨hs, hsum⟩, hps⟩ hbad
    have he := Finset.sum_erase_add s (fun x => x) hps
    refine no_rep_146 (s.erase p) (fun x hx => hs x (Finset.mem_of_mem_erase hx)) ?_
    omega
  · intro hgood
    have hex : (n - p, p) ∉ excL := fun h => by have := excL_small _ h; simp at this; omega
    obtain ⟨s, hs, hsum⟩ := rep_avoid (n - p) p (by omega) (by omega) (by omega) hex
    have hps : p ∉ s := fun h => (hs p h).2 rfl
    refine ⟨insert p s, ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hp
      · exact (hs x hx).1
    · rw [Finset.sum_insert hps, hsum]
      omega

theorem odd_of_prime_ge {q : ℕ} (hq : q.Prime) (h : 3 ≤ q) : q % 2 = 1 := by
  rcases hq.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

/-- **A054656 conjecture**, for every `n ≥ 23`. -/
theorem A054656_formula (n : ℕ) (hn : 23 ≤ n) :
    a n = if (n - 6).Prime ∧ (n - 4).Prime then 2
      else if (n - 6).Prime ∨ (n - 4).Prime ∨ (n - 1).Prime then 1 else 0 := by
  classical
  have hset : a n = (({n - 6, n - 4, n - 1} : Finset ℕ).filter Nat.Prime).card := by
    unfold a
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hpn, hp, hno⟩
      have := (not_congr (appears_iff hn hp (by omega))).mp hno
      push Not at this
      exact ⟨by omega, hp⟩
    · rintro ⟨h, hp⟩
      refine ⟨by omega, hp, ?_⟩
      rw [appears_iff hn hp (by omega)]
      omega
  rw [hset, Finset.card_filter, Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  have e14 : ¬ ((n - 1).Prime ∧ (n - 4).Prime) := by
    rintro ⟨h1, h4⟩
    have := odd_of_prime_ge h1 (by omega)
    have := odd_of_prime_ge h4 (by omega)
    omega
  have e16 : ¬ ((n - 1).Prime ∧ (n - 6).Prime) := by
    rintro ⟨h1, h6⟩
    have := odd_of_prime_ge h1 (by omega)
    have := odd_of_prime_ge h6 (by omega)
    omega
  by_cases h6 : (n - 6).Prime <;> by_cases h4 : (n - 4).Prime <;>
    by_cases h1 : (n - 1).Prime <;> simp_all

end A054656

open A054656
