import Mathlib
import OpenProblemsLib.ShortIntervalPrimes

/-
OEIS-A102237 (Mathlib). a(n) is the smallest number that is a product of n primes (with
multiplicity) and also a sum of n distinct primes. Conjecture (Ray Chandler, 2005):
a(n) = 2^n for n > 5.

Main theorem `A102237_main`: for every n ≥ 6, `a102237 n = 2 ^ n`, with `a102237` defined below as the
infimum in the entry's definition. `sum_distinct_primes`: 2^n is a sum of n distinct primes
for n ≥ 6.

Proof. `Win k L U M` says that every N ≡ k (mod 2) with L ≤ N ≤ U is a sum of k distinct
primes, each in [3, M]. `win_step`: from `Win k L U M` with M ≥ 25 and
0.42 M ≤ 1.21 (U - L) follows `Win (k + 1) (L + 1.21 M) (U + 2M/1.21) (2M)`: take the prime q
in (b, 1.21 b] for b = max(N - U, M) given by the library theorem
`OpenProblemsLib.ShortIntervalPrimes.exists_prime_Ioc_mul` (a prime in (x, 1.21 x] for real
x ≥ 25); then M < q ≤ 2M and N - q ∈ [L, U] has the parity of k, and q exceeds every prime
used for N - q. `win_chain` iterates this from k = 6 with two kernel-checked bases:
every even N in [62, 152] is a sum of six distinct odd primes ≤ 39 (`baseA`), and every even
N in [62, 374] of six distinct odd primes ≤ 78 (`baseB`). The first chain contains 2^n for
even n ≥ 6; the second contains 2^n - 2 for odd n ≥ 7, and 2^n = 2 + (2^n - 2).

Checked here (Lean 4.35.0, Mathlib 56a00585, axioms propext, Classical.choice, Quot.sound):
everything above, including the library prime bound (Chebyshev's method plus Pratt
certificates for 85 primes up to 118074017).

Outside Lean: none.
-/

open Finset OpenProblemsLib.ShortIntervalPrimes

/-- Every `N ≡ k (mod 2)` with `L ≤ N ≤ U` is a sum of `k` distinct primes, each in `[3, M]`. -/
def Win (k : ℕ) (L U M : ℝ) : Prop :=
  ∀ N : ℕ, N % 2 = k % 2 → L ≤ N → (N : ℝ) ≤ U →
    ∃ s : Finset ℕ, s.card = k ∧ (∀ p ∈ s, p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ M) ∧ ∑ p ∈ s, p = N

/-- One induction step: add a prime from `(M, 2M]`. -/
theorem win_step {k : ℕ} {L U M L' U' : ℝ} (h : Win k L U M) (hL : 0 ≤ L) (hM : 25 ≤ M)
    (hW : 0.42 * M ≤ 1.21 * (U - L)) (hL' : L + 1.21 * M ≤ L')
    (hU' : 1.21 * U' ≤ 1.21 * U + 2 * M) :
    Win (k + 1) L' U' (2 * M) := by
  intro N hN hLN hNU
  obtain ⟨q, hq, hbq, hqb⟩ :=
    exists_prime_Ioc_mul (max ((N : ℝ) - U) M) (le_trans hM (le_max_right _ _))
  have hMq : M < q := lt_of_le_of_lt (le_max_right _ _) hbq
  have hNUq : (N : ℝ) - U < q := lt_of_le_of_lt (le_max_left _ _) hbq
  have hq2M : (q : ℝ) ≤ 2 * M ∧ (q : ℝ) ≤ N - L := by
    rcases le_total ((N : ℝ) - U) M with hc | hc
    · rw [max_eq_right hc] at hqb
      constructor <;> linarith
    · rw [max_eq_left hc] at hqb
      constructor <;> linarith
  obtain ⟨hq2M, hqNL⟩ := hq2M
  have hq3 : 3 ≤ q := by
    have : (3 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hqN : q ≤ N := by
    have : (q : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have hcast : ((N - q : ℕ) : ℝ) = N - q := by push_cast [hqN]; ring
  obtain ⟨s, hs, hsp, hsum⟩ := h (N - q) (by omega) (by rw [hcast]; linarith)
    (by rw [hcast]; linarith)
  have hqs : q ∉ s := by
    intro hm
    have := (hsp q hm).2.2
    linarith
  refine ⟨insert q s, by rw [card_insert_of_notMem hqs, hs], ?_, ?_⟩
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact ⟨hq, hq3, hq2M⟩
    · obtain ⟨h1, h2, h3⟩ := hsp p hp
      exact ⟨h1, h2, by linarith⟩
  · rw [sum_insert hqs, hsum]
    omega

/-- Iterating `win_step` from a base window. -/
theorem win_chain {k0 : ℕ} {L0 U0 M0 : ℝ} (h : Win k0 L0 U0 M0) (hL : 0 ≤ L0) (hM : 25 ≤ M0)
    (hW : 0.42 * M0 ≤ 1.21 * (U0 - L0)) : ∀ j : ℕ,
    Win (k0 + j) (L0 + 1.21 * M0 * (2 ^ j - 1)) (U0 + 2 / 1.21 * M0 * (2 ^ j - 1))
      (M0 * 2 ^ j) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hM0 : 0 ≤ M0 * (2 ^ j - 1) := mul_nonneg (by linarith) (by linarith)
    have hs := win_step ih (by nlinarith) (by nlinarith)
      (by nlinarith) (L' := L0 + 1.21 * M0 * (2 ^ (j + 1) - 1))
      (le_of_eq (by rw [pow_succ]; ring)) (U' := U0 + 2 / 1.21 * M0 * (2 ^ (j + 1) - 1))
      (le_of_eq (by rw [pow_succ]; ring))
    rw [show k0 + (j + 1) = k0 + j + 1 by omega, show M0 * 2 ^ (j + 1) = 2 * (M0 * 2 ^ j) by
      rw [pow_succ]; ring]
    exact hs

/-! ## Base windows (kernel checked) -/

/-- The odd primes up to 78. -/
def oddPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

theorem oddPrimes_spec : ∀ p ∈ oddPrimes, p.Prime ∧ 3 ≤ p := by
  intro p hp
  simp only [oddPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- `w` lists six distinct odd primes `≤ M` with sum `N`. -/
def goodRep (M N : ℕ) (w : List ℕ) : Bool :=
  (w.length == 6) && decide w.Nodup && w.all (fun p => oddPrimes.contains p && decide (p ≤ M)) &&
    (w.sum == N)

/-- Row `i` of `tbl` represents `L + 2 i` for every `i < n`. -/
def baseCheck (M L n : ℕ) (tbl : List (List ℕ)) : Bool :=
  (List.range n).all (fun i => goodRep M (L + 2 * i) (tbl.getD i []))

theorem win_of_baseCheck (M L U n : ℕ) (tbl : List (List ℕ)) (hL : L % 2 = 0)
    (hU : U < L + 2 * n) (h : baseCheck M L n tbl = true) : Win 6 L U M := by
  intro N hN hLN hNU
  have hLN' : L ≤ N := by exact_mod_cast hLN
  have hNU' : N ≤ U := by exact_mod_cast hNU
  simp only [baseCheck, List.all_eq_true, List.mem_range] at h
  have hi := h ((N - L) / 2) (by omega)
  rw [show L + 2 * ((N - L) / 2) = N by omega] at hi
  set w := tbl.getD ((N - L) / 2) [] with hw
  simp only [goodRep, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at hi
  obtain ⟨⟨⟨hlen, hnd⟩, hall⟩, hsum⟩ := hi
  refine ⟨w.toFinset, by rw [List.toFinset_card_of_nodup hnd, hlen], ?_, ?_⟩
  · intro p hp
    rw [List.mem_toFinset] at hp
    obtain ⟨h1, h2⟩ := hall p hp
    obtain ⟨h3, h4⟩ := oddPrimes_spec p h1
    exact ⟨h3, h4, by exact_mod_cast h2⟩
  · rw [List.sum_toFinset _ hnd, List.map_id']
    exact hsum

/-- Witnesses for even N = 62, 64, …, 152: six distinct odd primes ≤ 39. -/
def baseA : List (List ℕ) :=
  [[3, 5, 7, 11, 13, 23], [3, 5, 7, 13, 17, 19], [3, 5, 7, 11, 17, 23], [3, 5, 7, 11, 13, 29],
   [3, 5, 7, 11, 13, 31], [3, 5, 7, 11, 17, 29], [3, 5, 7, 11, 17, 31], [3, 5, 7, 11, 13, 37],
   [3, 5, 7, 11, 23, 29], [3, 5, 7, 11, 17, 37], [3, 5, 7, 11, 19, 37], [3, 5, 7, 13, 19, 37],
   [3, 5, 7, 11, 23, 37], [3, 5, 7, 13, 23, 37], [3, 5, 11, 17, 23, 31], [3, 5, 7, 11, 29, 37],
   [3, 5, 7, 11, 31, 37], [3, 5, 7, 13, 31, 37], [3, 5, 7, 17, 29, 37], [3, 5, 7, 17, 31, 37],
   [3, 5, 7, 19, 31, 37], [3, 5, 7, 23, 29, 37], [3, 5, 7, 23, 31, 37], [3, 5, 11, 23, 29, 37],
   [3, 5, 11, 23, 31, 37], [3, 5, 7, 29, 31, 37], [3, 5, 17, 23, 29, 37], [3, 5, 11, 29, 31, 37],
   [3, 5, 13, 29, 31, 37], [3, 7, 13, 29, 31, 37], [3, 5, 17, 29, 31, 37],
   [3, 5, 19, 29, 31, 37], [3, 7, 19, 29, 31, 37], [3, 5, 23, 29, 31, 37],
   [3, 7, 23, 29, 31, 37], [3, 13, 19, 29, 31, 37], [3, 11, 23, 29, 31, 37],
   [3, 13, 23, 29, 31, 37], [5, 13, 23, 29, 31, 37], [3, 17, 23, 29, 31, 37],
   [3, 19, 23, 29, 31, 37], [5, 19, 23, 29, 31, 37], [7, 19, 23, 29, 31, 37],
   [11, 17, 23, 29, 31, 37], [11, 19, 23, 29, 31, 37], [13, 19, 23, 29, 31, 37]]

/-- Witnesses for even N = 62, 64, …, 374: six distinct odd primes ≤ 78. -/
def baseB : List (List ℕ) :=
  [[3, 5, 7, 11, 13, 23], [3, 5, 7, 13, 17, 19], [3, 5, 7, 11, 17, 23], [3, 5, 7, 11, 13, 29],
   [3, 5, 7, 11, 13, 31], [3, 5, 7, 11, 17, 29], [3, 5, 7, 11, 17, 31], [3, 5, 7, 11, 13, 37],
   [3, 5, 7, 11, 23, 29], [3, 5, 7, 11, 13, 41], [3, 5, 7, 11, 13, 43], [3, 5, 7, 11, 17, 41],
   [3, 5, 7, 11, 13, 47], [3, 5, 7, 11, 19, 43], [3, 5, 7, 11, 17, 47], [3, 5, 7, 11, 13, 53],
   [3, 5, 7, 11, 31, 37], [3, 5, 7, 11, 17, 53], [3, 5, 7, 11, 13, 59], [3, 5, 7, 11, 13, 61],
   [3, 5, 7, 11, 17, 59], [3, 5, 7, 11, 17, 61], [3, 5, 7, 11, 13, 67], [3, 5, 7, 11, 23, 59],
   [3, 5, 7, 11, 13, 71], [3, 5, 7, 11, 13, 73], [3, 5, 7, 11, 17, 71], [3, 5, 7, 11, 17, 73],
   [3, 5, 7, 11, 19, 73], [3, 5, 7, 11, 23, 71], [3, 5, 7, 11, 23, 73], [3, 5, 7, 11, 31, 67],
   [3, 5, 7, 11, 29, 71], [3, 5, 7, 11, 29, 73], [3, 5, 7, 11, 31, 73], [3, 5, 7, 11, 47, 59],
   [3, 5, 7, 11, 37, 71], [3, 5, 7, 11, 37, 73], [3, 5, 7, 11, 41, 71], [3, 5, 7, 11, 41, 73],
   [3, 5, 7, 11, 43, 73], [3, 5, 7, 11, 47, 71], [3, 5, 7, 11, 47, 73], [3, 5, 7, 13, 47, 73],
   [3, 5, 7, 11, 53, 71], [3, 5, 7, 11, 53, 73], [3, 5, 7, 11, 61, 67], [3, 5, 7, 11, 59, 71],
   [3, 5, 7, 11, 59, 73], [3, 5, 7, 11, 61, 73], [3, 5, 7, 13, 61, 73], [3, 5, 7, 11, 67, 71],
   [3, 5, 7, 11, 67, 73], [3, 5, 7, 13, 67, 73], [3, 5, 7, 11, 71, 73], [3, 5, 7, 13, 71, 73],
   [3, 5, 7, 19, 67, 73], [3, 5, 7, 17, 71, 73], [3, 5, 7, 19, 71, 73], [3, 5, 7, 31, 61, 73],
   [3, 5, 7, 23, 71, 73], [3, 5, 7, 29, 67, 73], [3, 5, 7, 31, 67, 73], [3, 5, 7, 29, 71, 73],
   [3, 5, 7, 31, 71, 73], [3, 5, 7, 37, 67, 73], [3, 5, 7, 41, 67, 71], [3, 5, 7, 37, 71, 73],
   [3, 5, 7, 43, 67, 73], [3, 5, 7, 41, 71, 73], [3, 5, 7, 43, 71, 73], [3, 5, 11, 41, 71, 73],
   [3, 5, 7, 47, 71, 73], [3, 5, 7, 53, 67, 73], [3, 5, 11, 47, 71, 73], [3, 5, 7, 53, 71, 73],
   [3, 5, 7, 59, 67, 73], [3, 5, 7, 61, 67, 73], [3, 5, 7, 59, 71, 73], [3, 5, 7, 61, 71, 73],
   [3, 5, 11, 59, 71, 73], [3, 5, 11, 61, 71, 73], [3, 5, 7, 67, 71, 73], [3, 5, 17, 59, 71, 73],
   [3, 5, 11, 67, 71, 73], [3, 5, 13, 67, 71, 73], [3, 5, 23, 59, 71, 73],
   [3, 5, 17, 67, 71, 73], [3, 5, 19, 67, 71, 73], [3, 5, 29, 59, 71, 73],
   [3, 5, 23, 67, 71, 73], [3, 5, 31, 61, 71, 73], [3, 5, 37, 61, 67, 73],
   [3, 5, 29, 67, 71, 73], [3, 5, 31, 67, 71, 73], [3, 5, 41, 59, 71, 73],
   [3, 5, 41, 61, 71, 73], [3, 5, 37, 67, 71, 73], [3, 5, 47, 59, 71, 73],
   [3, 5, 41, 67, 71, 73], [3, 5, 43, 67, 71, 73], [3, 5, 53, 59, 71, 73],
   [3, 5, 47, 67, 71, 73], [3, 5, 59, 61, 67, 73], [3, 7, 59, 61, 67, 73],
   [3, 5, 53, 67, 71, 73], [3, 7, 53, 67, 71, 73], [3, 13, 59, 61, 67, 73],
   [3, 5, 59, 67, 71, 73], [3, 5, 61, 67, 71, 73], [3, 7, 61, 67, 71, 73],
   [3, 11, 59, 67, 71, 73], [3, 11, 61, 67, 71, 73], [3, 13, 61, 67, 71, 73],
   [3, 17, 59, 67, 71, 73], [3, 17, 61, 67, 71, 73], [3, 19, 61, 67, 71, 73],
   [3, 23, 59, 67, 71, 73], [3, 23, 61, 67, 71, 73], [3, 37, 59, 61, 67, 73],
   [3, 29, 59, 67, 71, 73], [3, 29, 61, 67, 71, 73], [3, 31, 61, 67, 71, 73],
   [3, 41, 53, 67, 71, 73], [3, 37, 59, 67, 71, 73], [3, 37, 61, 67, 71, 73],
   [3, 41, 59, 67, 71, 73], [3, 41, 61, 67, 71, 73], [3, 43, 61, 67, 71, 73],
   [3, 47, 59, 67, 71, 73], [3, 47, 61, 67, 71, 73], [5, 47, 61, 67, 71, 73],
   [3, 53, 59, 67, 71, 73], [3, 53, 61, 67, 71, 73], [5, 53, 61, 67, 71, 73],
   [7, 53, 61, 67, 71, 73], [3, 59, 61, 67, 71, 73], [5, 59, 61, 67, 71, 73],
   [7, 59, 61, 67, 71, 73], [17, 53, 59, 67, 71, 73], [11, 59, 61, 67, 71, 73],
   [13, 59, 61, 67, 71, 73], [23, 53, 59, 67, 71, 73], [17, 59, 61, 67, 71, 73],
   [19, 59, 61, 67, 71, 73], [29, 53, 59, 67, 71, 73], [23, 59, 61, 67, 71, 73],
   [31, 53, 61, 67, 71, 73], [41, 47, 59, 67, 71, 73], [29, 59, 61, 67, 71, 73],
   [31, 59, 61, 67, 71, 73], [41, 53, 59, 67, 71, 73], [41, 53, 61, 67, 71, 73],
   [37, 59, 61, 67, 71, 73], [47, 53, 59, 67, 71, 73], [41, 59, 61, 67, 71, 73],
   [43, 59, 61, 67, 71, 73]]

theorem winA : Win 6 62 152 39 := by
  have := win_of_baseCheck 39 62 152 46 baseA (by norm_num) (by norm_num) (by decide +kernel)
  simpa using this

theorem winB : Win 6 62 374 78 := by
  have := win_of_baseCheck 78 62 374 157 baseB (by norm_num) (by norm_num) (by decide +kernel)
  simpa using this

/-! ## The theorem -/

/-- `2^n` is a sum of `n` distinct primes for every `n ≥ 6`. -/
theorem sum_distinct_primes (n : ℕ) (hn : 6 ≤ n) :
    ∃ s : Finset ℕ, s.card = n ∧ (∀ p ∈ s, p.Prime) ∧ ∑ p ∈ s, p = 2 ^ n := by
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  rcases Nat.even_or_odd n with hev | hod
  · -- even n: 2^n is a sum of n distinct odd primes (chain A)
    have hev2 : n % 2 = 0 := Nat.even_iff.mp hev
    have hc := win_chain winA (by norm_num) (by norm_num) (by norm_num) (n - 6)
    rw [show 6 + (n - 6) = n by omega] at hc
    have ht : (1 : ℝ) ≤ 2 ^ (n - 6) := one_le_pow₀ (by norm_num)
    have hpow : ((2 ^ n : ℕ) : ℝ) = 64 * 2 ^ (n - 6) := by
      rw [show n = 6 + (n - 6) by omega]; push_cast; rw [pow_add]; norm_num
    obtain ⟨s, hs, hsp, hsum⟩ := hc (2 ^ n) (by omega) (by rw [hpow]; nlinarith)
      (by rw [hpow]; nlinarith)
    exact ⟨s, hs, fun p hp => (hsp p hp).1, hsum⟩
  · -- odd n: 2^n = 2 + (sum of n - 1 distinct odd primes) (chain B)
    have hod2 : n % 2 = 1 := Nat.odd_iff.mp hod
    have hn7 : 7 ≤ n := by omega
    have hc := win_chain winB (by norm_num) (by norm_num) (by norm_num) (n - 7)
    rw [show 6 + (n - 7) = n - 1 by omega] at hc
    have ht : (1 : ℝ) ≤ 2 ^ (n - 7) := one_le_pow₀ (by norm_num)
    have h2le : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : ((2 ^ n - 2 : ℕ) : ℝ) = 128 * 2 ^ (n - 7) - 2 := by
      rw [Nat.cast_sub h2le, show n = 7 + (n - 7) by omega]; push_cast; rw [pow_add]; norm_num
    obtain ⟨s, hs, hsp, hsum⟩ := hc (2 ^ n - 2) (by omega) (by rw [hpow]; nlinarith)
      (by rw [hpow]; nlinarith)
    have h2s : 2 ∉ s := by
      intro hm
      have := (hsp 2 hm).2.1
      omega
    refine ⟨insert 2 s, by rw [card_insert_of_notMem h2s, hs]; omega, ?_, ?_⟩
    · intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact Nat.prime_two
      · exact (hsp p hp).1
    · rw [sum_insert h2s, hsum]
      omega

/-- `m` is a product of `n` primes (counted with multiplicity). -/
def IsProdPrimes (n m : ℕ) : Prop :=
  ∃ l : List ℕ, l.length = n ∧ (∀ p ∈ l, p.Prime) ∧ l.prod = m

/-- `m` is a sum of `n` distinct primes. -/
def IsSumDistinctPrimes (n m : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = n ∧ (∀ p ∈ s, p.Prime) ∧ ∑ p ∈ s, p = m

/-- A102237: the smallest number that is a product of `n` primes and a sum of `n` distinct
primes (`0` if there is none). -/
noncomputable def a102237 (n : ℕ) : ℕ := sInf {m | IsProdPrimes n m ∧ IsSumDistinctPrimes n m}

theorem two_pow_le_prod : ∀ l : List ℕ, (∀ p ∈ l, p.Prime) → 2 ^ l.length ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p l ih =>
    intro h
    rw [List.length_cons, List.prod_cons, pow_succ']
    exact Nat.mul_le_mul (h p (by simp)).two_le (ih (fun q hq => h q (by simp [hq])))

/-- **A102237**: `a102237 n = 2 ^ n` for every `n ≥ 6`. -/
theorem A102237_main (n : ℕ) (hn : 6 ≤ n) : a102237 n = 2 ^ n := by
  have hmem : 2 ^ n ∈ {m | IsProdPrimes n m ∧ IsSumDistinctPrimes n m} := by
    refine ⟨⟨List.replicate n 2, by simp, ?_, by simp⟩, sum_distinct_primes n hn⟩
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    exact Nat.prime_two
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro m ⟨⟨l, hl, hp, rfl⟩, _⟩
  rw [← hl]
  exact two_pow_le_prod l hp

