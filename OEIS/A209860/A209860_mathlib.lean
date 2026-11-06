/-
OEIS A209860, A209861, A209862: the binary complement A054429 commutes with the
permutation A209861 (and its inverse A209862).

Definitions follow the entries.
- A209642: Karttunen's Scheme loop (s, i) -> (4s+1, 4i) on a 0-bit, (2(s+i), 4i) on a 1-bit,
  reading n from the least significant bit.
- A209641 is the list of values of A209642 in ascending order, so A209861(n), the position of
  A209642(n) in A209641 (offset 0), is the number of values of A209642 below A209642(n)
  (Set.ncard).  A209862 is the inverse permutation (Function.invFun; A209861 is proved bijective).
- A054429(n) = 3 * 2^floor(log2 n) - 1 - n (offset 1, reverse each block [2^k, 2^(k+1))).
- A209860 = fixed points of A209861.
Checked here (n >= 1): A209861_conjecture, A209862_conjecture, A209860_conjecture.
Proof: closed form A209642(n) + 2^E = 2^(2 len n) + tau(n), E = 2 len - pop, 2 tau < 2^E;
so on one level the values are ordered by popcount, then by tau, and A054429 reverses both.
Not checked here: that the A209641 membership test of the entry gives exactly the values
of A209642 (certificate/check.py checks it below 4^8), and agreement with the b-files.
-/
import Mathlib

namespace A209860

open Finset

/-- A209642, the entry's Scheme loop. -/
def loop (n s i : ℕ) : ℕ :=
  if h : n = 0 then s
  else if n % 2 = 0 then loop (n / 2) (4 * s + 1) (4 * i)
  else loop (n / 2) (2 * (s + i)) (4 * i)
termination_by n
decreasing_by all_goals omega

def A209642 (n : ℕ) : ℕ := loop n 0 1

/-- Binary length. -/
def len (n : ℕ) : ℕ := if h : n = 0 then 0 else len (n / 2) + 1
termination_by n
decreasing_by omega

/-- Number of 1-bits. -/
def pop (n : ℕ) : ℕ := if h : n = 0 then 0 else pop (n / 2) + n % 2
termination_by n
decreasing_by omega

def E (n : ℕ) : ℕ := 2 * len n - pop n

def tau (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else if n % 2 = 1 then tau (n / 2) else 2 ^ E (n / 2) + tau (n / 2)
termination_by n
decreasing_by all_goals omega

theorem loop_zero (s i : ℕ) : loop 0 s i = s := by
  rw [loop]; simp

theorem loop_even (q s i : ℕ) (hq : 1 ≤ q) : loop (2 * q) s i = loop q (4 * s + 1) (4 * i) := by
  rw [loop]
  split
  · omega
  · split
    · congr 1; omega
    · omega

theorem loop_odd (q s i : ℕ) : loop (2 * q + 1) s i = loop q (2 * (s + i)) (4 * i) := by
  rw [loop]
  split
  · omega
  · split
    · omega
    · congr 1; omega

theorem len_zero : len 0 = 0 := by rw [len]; simp

theorem len_even (q : ℕ) (hq : 1 ≤ q) : len (2 * q) = len q + 1 := by
  rw [len]
  split
  · omega
  · congr 2; omega

theorem len_odd (q : ℕ) : len (2 * q + 1) = len q + 1 := by
  rw [len]
  split
  · omega
  · congr 2; omega

theorem pop_zero : pop 0 = 0 := by rw [pop]; simp

theorem pop_even (q : ℕ) (hq : 1 ≤ q) : pop (2 * q) = pop q := by
  rw [pop]
  split
  · omega
  · have : 2 * q / 2 = q := by omega
    rw [this]; omega

theorem pop_odd (q : ℕ) : pop (2 * q + 1) = pop q + 1 := by
  rw [pop]
  split
  · omega
  · have : (2 * q + 1) / 2 = q := by omega
    rw [this]; omega

theorem tau_even (q : ℕ) (hq : 1 ≤ q) : tau (2 * q) = 2 ^ E q + tau q := by
  rw [tau]
  split
  · omega
  · split
    · omega
    · have : 2 * q / 2 = q := by omega
      rw [this]

theorem tau_odd (q : ℕ) : tau (2 * q + 1) = tau q := by
  rw [tau]
  split
  · omega
  · split
    · congr 1; omega
    · omega

/-- Induction over n >= 1 by the last binary digit. -/
theorem bin_induction {p : ℕ → Prop} (h1 : p 1) (h0 : ∀ q, 1 ≤ q → p q → p (2 * q))
    (h1' : ∀ q, 1 ≤ q → p q → p (2 * q + 1)) : ∀ n, 1 ≤ n → p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact h0 q (by omega) (ih q (by omega) (by omega))
    · rcases Nat.eq_zero_or_pos q with rfl | hq
      · exact h1
      · exact h1' q hq (ih q (by omega) hq)

theorem len_one : len 1 = 1 := by simpa [len_zero] using len_odd 0

theorem pop_one : pop 1 = 1 := by simpa [pop_zero] using pop_odd 0

theorem tau_zero : tau 0 = 0 := by rw [tau]; simp

theorem tau_one : tau 1 = 0 := by simpa [tau_zero] using tau_odd 0

theorem pop_le_len (n : ℕ) : pop n ≤ len n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pop_zero, len_zero]
  · revert n
    refine bin_induction (by simp [pop_one, len_one]) ?_ ?_
    · intro q hq ih; rw [pop_even q hq, len_even q hq]; omega
    · intro q _ ih; rw [pop_odd, len_odd]; omega

theorem len_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ len n ∧ 1 ≤ pop n := by
  revert n
  refine bin_induction (by simp [pop_one, len_one]) ?_ ?_
  · intro q hq ih; rw [pop_even q hq, len_even q hq]; omega
  · intro q _ ih; rw [pop_odd, len_odd]; omega

theorem E_even (q : ℕ) (hq : 1 ≤ q) : E (2 * q) = E q + 2 := by
  unfold E; rw [len_even q hq, pop_even q hq]; have := pop_le_len q; omega

theorem E_odd (q : ℕ) : E (2 * q + 1) = E q + 1 := by
  unfold E; rw [len_odd, pop_odd]; have := pop_le_len q; omega

theorem E_add_pop (n : ℕ) : E n + pop n = 2 * len n := by
  unfold E; have := pop_le_len n; omega

/-- Bounds 2^(len n - 1) <= n < 2^(len n). -/
theorem len_bounds (n : ℕ) (hn : 1 ≤ n) : 2 ^ (len n - 1) ≤ n ∧ n < 2 ^ len n := by
  revert n
  refine bin_induction (by simp [len_one]) ?_ ?_
  · intro q hq ih
    rw [len_even q hq]
    have h1 := (len_pos q hq).1
    have : 2 ^ (len q + 1 - 1) = 2 * 2 ^ (len q - 1) := by
      rw [show len q + 1 - 1 = (len q - 1) + 1 by omega, pow_succ]; ring
    rw [this, pow_succ]; omega
  · intro q hq ih
    rw [len_odd]
    have h1 := (len_pos q hq).1
    have : 2 ^ (len q + 1 - 1) = 2 * 2 ^ (len q - 1) := by
      rw [show len q + 1 - 1 = (len q - 1) + 1 by omega, pow_succ]; ring
    rw [this, pow_succ]; omega

theorem len_eq_of_bounds (n L : ℕ) (hL : 1 ≤ L) (h1 : 2 ^ (L - 1) ≤ n) (h2 : n < 2 ^ L) :
    len n = L := by
  have hn : 1 ≤ n := le_trans Nat.one_le_two_pow h1
  obtain ⟨b1, b2⟩ := len_bounds n hn
  rcases lt_trichotomy (len n) L with h | h | h
  · have : 2 ^ len n ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact h
  · have : 2 ^ L ≤ 2 ^ (len n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- Closed form of the loop. -/
theorem loop_closed (n : ℕ) (hn : 1 ≤ n) : ∀ s t : ℕ,
    loop n s (4 ^ t) + 4 ^ t * 2 ^ E n = 4 ^ t * 2 ^ E n * 2 ^ pop n + s * 2 ^ E n + tau n := by
  revert n
  refine bin_induction ?_ ?_ ?_
  · intro s t
    rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, loop_odd, loop_zero, E_odd, pop_odd, tau_odd]
    simp [E, len_zero, pop_zero, tau_zero]
    ring
  · intro q hq ih s t
    rw [loop_even q s _ hq, E_even q hq, pop_even q hq, tau_even q hq]
    have := ih (4 * s + 1) (t + 1)
    rw [pow_succ] at this
    rw [show 4 * 4 ^ t = 4 ^ t * 4 by ring,
      show 2 ^ (E q + 2) = 2 ^ E q * 4 by rw [pow_add]; norm_num]
    nlinarith [this]
  · intro q hq ih s t
    rw [loop_odd, E_odd, pop_odd, tau_odd]
    have := ih (2 * (s + 4 ^ t)) (t + 1)
    rw [pow_succ] at this
    rw [show 4 * 4 ^ t = 4 ^ t * 4 by ring, pow_succ 2 (E q), pow_succ 2 (pop q)]
    nlinarith [this]

theorem g_closed (n : ℕ) (hn : 1 ≤ n) :
    A209642 n + 2 ^ E n = 2 ^ (2 * len n) + tau n := by
  have := loop_closed n hn 0 0
  simp only [pow_zero, one_mul, zero_mul, add_zero] at this
  rw [A209642, ← E_add_pop, pow_add]
  simpa using this

theorem tau_lt (n : ℕ) (hn : 1 ≤ n) : 2 * tau n < 2 ^ E n := by
  revert n
  refine bin_induction ?_ ?_ ?_
  · rw [tau_one]; positivity
  · intro q hq ih
    rw [tau_even q hq, E_even q hq, pow_add]
    omega
  · intro q hq ih
    rw [tau_odd, E_odd, pow_succ]
    omega

/-- Level bounds of A209642: 2^(2L-1) <= g n < 2^(2L). -/
theorem g_bounds (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (2 * len n - 1) ≤ A209642 n ∧ A209642 n < 2 ^ (2 * len n) := by
  have h1 := g_closed n hn
  have h2 := tau_lt n hn
  have hp := (len_pos n hn).2
  have hE := E_add_pop n
  have : 2 ^ E n ≤ 2 ^ (2 * len n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2 * len n) = 2 * 2 ^ (2 * len n - 1) := by
    rw [← pow_succ']; congr 1; have := (len_pos n hn).1; omega
  omega

theorem g_zero : A209642 0 = 0 := by simp [A209642, loop_zero]

/-- Odd n beats even n' on the same level with the same popcount. -/
theorem tau_odd_lt_even (q q' : ℕ) (hq' : 1 ≤ q') (hl : len (2 * q + 1) = len (2 * q'))
    (hp : pop (2 * q + 1) = pop (2 * q')) : tau (2 * q + 1) < tau (2 * q') := by
  rw [tau_odd, tau_even q' hq']
  rw [len_odd, len_even q' hq'] at hl
  rw [pop_odd, pop_even q' hq'] at hp
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [tau_zero]; positivity
  · have h1 := tau_lt q hq
    have h2 : E q = E q' + 1 := by
      unfold E; have := pop_le_len q'; have := pop_le_len q; omega
    rw [h2, pow_succ] at h1
    omega

/-- A054429 (offset 1): reverse each block [2^k, 2^(k+1)). -/
def A054429 (n : ℕ) : ℕ := 3 * 2 ^ Nat.log 2 n - 1 - n

theorem log_eq (n : ℕ) (hn : 1 ≤ n) : Nat.log 2 n = len n - 1 := by
  obtain ⟨h1, h2⟩ := len_bounds n hn
  have := (len_pos n hn).1
  apply Nat.log_eq_of_pow_le_of_lt_pow h1
  rwa [show len n - 1 + 1 = len n by omega]

theorem c_formula (n : ℕ) (hn : 1 ≤ n) : A054429 n = 3 * 2 ^ (len n - 1) - 1 - n := by
  rw [A054429, log_eq n hn]

theorem c_props (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ A054429 n ∧ len (A054429 n) = len n ∧ A054429 (A054429 n) = n := by
  obtain ⟨h1, h2⟩ := len_bounds n hn
  have hL := (len_pos n hn).1
  have hP : 2 ^ len n = 2 * 2 ^ (len n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc := c_formula n hn
  have hlen : len (A054429 n) = len n :=
    len_eq_of_bounds _ _ hL (by omega) (by omega)
  have hc1 : 1 ≤ A054429 n := by have := Nat.one_le_two_pow (n := len n - 1); omega
  refine ⟨hc1, hlen, ?_⟩
  rw [c_formula _ hc1, hlen, hc]
  omega

theorem c_even (q : ℕ) (hq : 1 ≤ q) : A054429 (2 * q) = 2 * A054429 q + 1 := by
  rw [c_formula _ (by omega), c_formula _ hq, len_even q hq]
  obtain ⟨h1, h2⟩ := len_bounds q hq
  have hL := (len_pos q hq).1
  have hP : 2 ^ (len q + 1 - 1) = 2 * 2 ^ (len q - 1) := by
    rw [show len q + 1 - 1 = len q - 1 + 1 by omega, pow_succ]; ring
  have hP' : 2 ^ len q = 2 * 2 ^ (len q - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem c_odd (q : ℕ) (hq : 1 ≤ q) : A054429 (2 * q + 1) = 2 * A054429 q := by
  rw [c_formula _ (by omega), c_formula _ hq, len_odd]
  obtain ⟨h1, h2⟩ := len_bounds q hq
  have hL := (len_pos q hq).1
  have hP : 2 ^ (len q + 1 - 1) = 2 * 2 ^ (len q - 1) := by
    rw [show len q + 1 - 1 = len q - 1 + 1 by omega, pow_succ]; ring
  have hP' : 2 ^ len q = 2 * 2 ^ (len q - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem c_one : A054429 1 = 1 := by
  rw [c_formula 1 le_rfl, len_one]
  norm_num

theorem pop_c (n : ℕ) (hn : 1 ≤ n) : pop (A054429 n) + pop n = len n + 1 := by
  revert n
  refine bin_induction (by rw [c_one, pop_one, len_one]) ?_ ?_
  · intro q hq ih
    have := (c_props q hq).1
    rw [c_even q hq, pop_odd, pop_even q hq, len_even q hq]; omega
  · intro q hq ih
    have := (c_props q hq).1
    rw [c_odd q hq, pop_even _ this, pop_odd, len_odd]; omega

/-- Same level, same popcount: tau order reverses under A054429, and tau is injective. -/
theorem tau_c (n : ℕ) (hn : 1 ≤ n) : ∀ n', 1 ≤ n' → len n = len n' → pop n = pop n' →
    ((tau n < tau n' ↔ tau (A054429 n') < tau (A054429 n)) ∧ (tau n = tau n' → n = n')) := by
  revert n
  refine bin_induction ?_ ?_ ?_
  · intro n' hn' hl hp
    rw [len_one] at hl
    obtain ⟨b1, b2⟩ := len_bounds n' hn'
    rw [← hl] at b2
    have : n' = 1 := by omega
    subst this
    simp
  · intro q hq ih n' hn' hl hp
    obtain ⟨q', b, rfl | rfl⟩ : ∃ q' b, n' = 2 * q' ∨ n' = 2 * q' + 1 := by
      obtain ⟨q', h⟩ := Nat.even_or_odd' n'; exact ⟨q', 0, by omega⟩
    · have hq' : 1 ≤ q' := by omega
      rw [len_even q hq, len_even q' hq'] at hl
      rw [pop_even q hq, pop_even q' hq'] at hp
      obtain ⟨i1, i2⟩ := ih q' hq' (by omega) hp
      have hcq := c_props q hq
      have hcq' := c_props q' hq'
      have hEq : E q = E q' := by unfold E; omega
      rw [c_even q hq, c_even q' hq', tau_odd, tau_odd, tau_even q hq, tau_even q' hq', hEq]
      constructor
      · rw [← i1]; omega
      · intro h; have := i2 (by omega); omega
    · have hl0 := hl
      have hp0 := hp
      rw [len_even q hq, len_odd] at hl
      rw [pop_even q hq, pop_odd] at hp
      rcases Nat.eq_zero_or_pos q' with rfl | hq'
      · rw [len_zero] at hl; have := (len_pos q hq).1; omega
      have hlt := tau_odd_lt_even q' q hq hl0.symm hp0.symm
      have hcq := c_props q hq
      have hcq' := c_props q' hq'
      have hlt2 := tau_odd_lt_even (A054429 q) (A054429 q') hcq'.1
        (by rw [len_odd, len_even _ hcq'.1, hcq.2.1, hcq'.2.1]; omega)
        (by
          rw [pop_odd, pop_even _ hcq'.1]
          have := pop_c q hq; have := pop_c q' hq'; omega)
      rw [c_even q hq, c_odd q' hq']
      refine ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩
  · intro q hq ih n' hn' hl hp
    obtain ⟨q', b, rfl | rfl⟩ : ∃ q' b, n' = 2 * q' ∨ n' = 2 * q' + 1 := by
      obtain ⟨q', h⟩ := Nat.even_or_odd' n'; exact ⟨q', 0, by omega⟩
    · have hq' : 1 ≤ q' := by omega
      have hlt := tau_odd_lt_even q q' hq' hl hp
      have hl0 := hl
      have hp0 := hp
      rw [len_odd, len_even q' hq'] at hl
      rw [pop_odd, pop_even q' hq'] at hp
      have hcq := c_props q hq
      have hcq' := c_props q' hq'
      have hlt2 := tau_odd_lt_even (A054429 q') (A054429 q) hcq.1
        (by rw [len_odd, len_even _ hcq.1, hcq.2.1, hcq'.2.1]; omega)
        (by
          rw [pop_odd, pop_even _ hcq.1]
          have := pop_c q hq; have := pop_c q' hq'; omega)
      rw [c_odd q hq, c_even q' hq']
      refine ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩
    · rcases Nat.eq_zero_or_pos q' with rfl | hq'
      · rw [len_odd, len_odd, len_zero] at hl; have := (len_pos q hq).1; omega
      rw [len_odd, len_odd] at hl
      rw [pop_odd, pop_odd] at hp
      obtain ⟨i1, i2⟩ := ih q' hq' (by omega) (by omega)
      have hcq := c_props q hq
      have hcq' := c_props q' hq'
      have hEq : E (A054429 q) = E (A054429 q') := by
        unfold E; rw [hcq.2.1, hcq'.2.1]
        have := pop_c q hq; have := pop_c q' hq'; omega
      rw [c_odd q hq, c_odd q' hq', tau_odd, tau_odd, tau_even _ hcq.1, tau_even _ hcq'.1, hEq]
      constructor
      · rw [i1]; omega
      · intro h; have := i2 h; omega

theorem g_lt_of_pop_lt (n n' : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n') (hl : len n = len n')
    (hp : pop n < pop n') : A209642 n < A209642 n' := by
  have h1 := g_closed n hn
  have h2 := g_closed n' hn'
  have h3 := tau_lt n hn
  have e1 := E_add_pop n
  have e2 := E_add_pop n'
  have h4 : 2 * 2 ^ E n' ≤ 2 ^ E n := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hl] at h1
  omega

theorem g_lt_iff_tau (n n' : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n') (hl : len n = len n')
    (hp : pop n = pop n') : (A209642 n < A209642 n' ↔ tau n < tau n') ∧
      (A209642 n = A209642 n' ↔ tau n = tau n') := by
  have h1 := g_closed n hn
  have h2 := g_closed n' hn'
  have hE : E n = E n' := by unfold E; rw [hl, hp]
  rw [hl, hE] at h1
  constructor <;> constructor <;> intro h <;> omega

/-- The key lemma: on one level, A054429 reverses the order of A209642 values. -/
theorem g_c (n n' : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n') (hl : len n = len n') :
    (A209642 n < A209642 n' ↔ A209642 (A054429 n') < A209642 (A054429 n)) ∧
      (A209642 n = A209642 n' → n = n') := by
  have hc := c_props n hn
  have hc' := c_props n' hn'
  have p1 := pop_c n hn
  have p2 := pop_c n' hn'
  have hlc : len (A054429 n') = len (A054429 n) := by rw [hc.2.1, hc'.2.1, hl]
  rcases lt_trichotomy (pop n) (pop n') with h | h | h
  · have a1 := g_lt_of_pop_lt n n' hn hn' hl h
    have a2 := g_lt_of_pop_lt (A054429 n') (A054429 n) hc'.1 hc.1 hlc (by omega)
    exact ⟨⟨fun _ => a2, fun _ => a1⟩, fun he => by omega⟩
  · have t := tau_c n hn n' hn' hl h
    have u := g_lt_iff_tau n n' hn hn' hl h
    have v := g_lt_iff_tau (A054429 n') (A054429 n) hc'.1 hc.1 hlc (by omega)
    refine ⟨?_, fun he => t.2 (u.2.1 he)⟩
    rw [u.1, v.1]; exact t.1
  · have a1 := g_lt_of_pop_lt n' n hn' hn hl.symm h
    have a2 := g_lt_of_pop_lt (A054429 n) (A054429 n') hc.1 hc'.1 hlc.symm (by omega)
    exact ⟨⟨fun h' => by omega, fun h' => by omega⟩, fun he => by omega⟩

/-- A209642 is injective. -/
theorem g_inj (n n' : ℕ) (h : A209642 n = A209642 n') : n = n' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos n' with rfl | hn'
    · rfl
    · have := (g_bounds n' hn').1; rw [g_zero] at h
      have : 1 ≤ 2 ^ (2 * len n' - 1) := Nat.one_le_two_pow; omega
  rcases Nat.eq_zero_or_pos n' with rfl | hn'
  · have := (g_bounds n hn).1; rw [g_zero] at h
    have : 1 ≤ 2 ^ (2 * len n - 1) := Nat.one_le_two_pow; omega
  rcases lt_trichotomy (len n) (len n') with hl | hl | hl
  · have b1 := (g_bounds n hn).2
    have b2 := (g_bounds n' hn').1
    have : 2 ^ (2 * len n) ≤ 2 ^ (2 * len n' - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact (g_c n n' hn hn' hl).2 h
  · have b1 := (g_bounds n' hn').2
    have b2 := (g_bounds n hn).1
    have : 2 ^ (2 * len n') ≤ 2 ^ (2 * len n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- A209861(n): position of A209642(n) in A209641 (= the values of A209642 in ascending order),
i.e. the number of values of A209642 below A209642(n). -/
noncomputable def A209861 (n : ℕ) : ℕ := Set.ncard {i | A209642 i < A209642 n}

/-- Within-level rank. -/
def rk (n : ℕ) : ℕ :=
  ((Ico (2 ^ (len n - 1)) (2 ^ len n)).filter (fun i => A209642 i < A209642 n)).card

theorem A209861_eq (n : ℕ) (hn : 1 ≤ n) : A209861 n = 2 ^ (len n - 1) + rk n := by
  have hL := (len_pos n hn).1
  have hP : 2 ^ len n = 2 * 2 ^ (len n - 1) := by rw [← pow_succ']; congr 1; omega
  have gb := g_bounds n hn
  have hset : {i | A209642 i < A209642 n} =
      ↑(range (2 ^ (len n - 1)) ∪
        (Ico (2 ^ (len n - 1)) (2 ^ len n)).filter (fun i => A209642 i < A209642 n)) := by
    ext i
    simp only [Set.mem_ofPred_eq, coe_union, coe_range, coe_filter, Set.mem_union, Set.mem_Iio,
      mem_Ico, Set.mem_ofPred_eq]
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · left; positivity
      obtain ⟨b1, b2⟩ := len_bounds i hi
      have gi := g_bounds i hi
      rcases lt_trichotomy (len i) (len n) with hl | hl | hl
      · left
        have : 2 ^ len i ≤ 2 ^ (len n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · right; rw [← hl]; exact ⟨⟨b1, b2⟩, h⟩
      · exfalso
        have : 2 ^ (2 * len n) ≤ 2 ^ (2 * len i - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · rintro (h | ⟨_, h⟩)
      · rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [g_zero]; have : 1 ≤ 2 ^ (2 * len n - 1) := Nat.one_le_two_pow; omega
        obtain ⟨b1, b2⟩ := len_bounds i hi
        have gi := g_bounds i hi
        have hli : len i < len n := by
          by_contra hc
          have : 2 ^ (len n - 1) ≤ 2 ^ (len i - 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (2 * len i) ≤ 2 ^ (2 * len n - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · exact h
  rw [A209861, hset, Set.ncard_coe_finset, card_union_of_disjoint, card_range, rk]
  rw [Finset.disjoint_left]
  intro i h1 h2
  simp only [mem_range, mem_filter, mem_Ico] at h1 h2
  omega

theorem rk_lt (n : ℕ) (hn : 1 ≤ n) : rk n < 2 ^ (len n - 1) := by
  have hL := (len_pos n hn).1
  have hP : 2 ^ len n = 2 * 2 ^ (len n - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨b1, b2⟩ := len_bounds n hn
  have hsub : (Ico (2 ^ (len n - 1)) (2 ^ len n)).filter (fun i => A209642 i < A209642 n) ⊂
      Ico (2 ^ (len n - 1)) (2 ^ len n) := by
    refine ⟨filter_subset _ _, fun h => ?_⟩
    have := h (mem_Ico.2 ⟨b1, b2⟩)
    simp at this
  have := card_lt_card hsub
  rw [Nat.card_Ico] at this
  unfold rk
  omega

theorem rk_c (n : ℕ) (hn : 1 ≤ n) : rk (A054429 n) + rk n + 1 = 2 ^ (len n - 1) := by
  have hc := c_props n hn
  have hL := (len_pos n hn).1
  have hP : 2 ^ len n = 2 * 2 ^ (len n - 1) := by rw [← pow_succ']; congr 1; omega
  set P := 2 ^ (len n - 1) with hPdef
  set I := Ico P (2 ^ len n) with hI
  have memI : ∀ i, i ∈ I ↔ 1 ≤ i ∧ len i = len n := by
    intro i
    rw [hI, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      have : 1 ≤ P := Nat.one_le_two_pow
      exact ⟨by omega, len_eq_of_bounds i _ hL h1 h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨b1, b2⟩ := len_bounds i h1
      rw [h2] at b1 b2
      exact ⟨b1, b2⟩
  have e1 : rk (A054429 n) = (I.filter (fun j => A209642 n < A209642 j)).card := by
    unfold rk
    rw [hc.2.1]
    refine card_bij' (fun i _ => A054429 i) (fun j _ => A054429 j) ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_filter] at hi ⊢
      have hi1 := (memI i).1 hi.1
      have ci := c_props i hi1.1
      refine ⟨(memI _).2 ⟨ci.1, by rw [ci.2.1, hi1.2]⟩, ?_⟩
      have := (g_c n (A054429 i) hn ci.1 (by rw [ci.2.1, hi1.2])).1
      rw [ci.2.2] at this
      exact this.2 hi.2
    · intro j hj
      rw [mem_filter] at hj ⊢
      have hj1 := (memI j).1 hj.1
      have cj := c_props j hj1.1
      refine ⟨(memI _).2 ⟨cj.1, by rw [cj.2.1, hj1.2]⟩, ?_⟩
      exact ((g_c n j hn hj1.1 hj1.2.symm).1).1 hj.2
    · intro i hi
      exact (c_props i ((memI i).1 (mem_filter.1 hi).1).1).2.2
    · intro j hj
      exact (c_props j ((memI j).1 (mem_filter.1 hj).1).1).2.2
  have e2 : (I.filter (fun i => ¬ A209642 i < A209642 n)) =
      insert n (I.filter (fun j => A209642 n < A209642 j)) := by
    ext i
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hi, h⟩
      rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
      · exact Or.inr ⟨hi, h'⟩
      · left
        have hi1 := (memI i).1 hi
        exact ((g_c n i hn hi1.1 hi1.2.symm).2 h').symm
    · rintro (rfl | ⟨hi, h⟩)
      · exact ⟨(memI _).2 ⟨hn, rfl⟩, lt_irrefl _⟩
      · exact ⟨hi, not_lt.2 h.le⟩
  have e3 := card_filter_add_card_filter_not (s := I) (fun i => A209642 i < A209642 n)
  rw [e2, card_insert_of_notMem (by simp)] at e3
  have hIc : I.card = 2 ^ len n - P := by rw [hI, Nat.card_Ico]
  rw [hIc] at e3
  have e4 : rk n = (I.filter (fun i => A209642 i < A209642 n)).card := rfl
  rw [e1, e4]
  omega

/-- A209861 commutes with A054429. -/
theorem A209861_conj (n : ℕ) (hn : 1 ≤ n) : A209861 (A054429 n) = A054429 (A209861 n) := by
  have hc := c_props n hn
  have hL := (len_pos n hn).1
  have hP : 2 ^ len n = 2 * 2 ^ (len n - 1) := by rw [← pow_succ']; congr 1; omega
  have r1 := rk_c n hn
  have r2 := rk_lt n hn
  rw [A209861_eq _ hc.1, A209861_eq n hn, hc.2.1]
  have hm : 1 ≤ 2 ^ (len n - 1) + rk n := by have : 1 ≤ 2 ^ (len n - 1) := Nat.one_le_two_pow; omega
  have hlm : len (2 ^ (len n - 1) + rk n) = len n := len_eq_of_bounds _ _ hL (by omega) (by omega)
  rw [c_formula _ hm, hlm]
  omega

theorem A209861_zero : A209861 0 = 0 := by
  simp [A209861, g_zero]

theorem A209861_inj : Function.Injective A209861 := by
  have key : ∀ n n', A209642 n < A209642 n' → A209861 n < A209861 n' := by
    intro n n' h
    have hn' : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with rfl | h'
      · rw [g_zero] at h; omega
      · exact h'
    have hfin : {i | A209642 i < A209642 n'}.Finite := by
      apply (Set.finite_Iio (2 ^ len n')).subset
      intro i hi
      simp only [Set.mem_ofPred_eq, Set.mem_Iio] at hi ⊢
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · positivity
      by_contra hc
      have b := len_bounds i hi0
      have hl : len n' + 1 ≤ len i := by
        by_contra hc'
        have : 2 ^ len i ≤ 2 ^ len n' := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have g1 := (g_bounds i hi0).1
      have g2 := (g_bounds n' hn').2
      have : 2 ^ (2 * len n') ≤ 2 ^ (2 * len i - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply Set.ncard_lt_ncard _ hfin
    refine ⟨fun i hi => lt_trans hi h, fun hsub => ?_⟩
    have := hsub (show n ∈ {i | A209642 i < A209642 n'} from h)
    simp at this
  intro n n' h
  rcases lt_trichotomy (A209642 n) (A209642 n') with h' | h' | h'
  · have := key n n' h'; omega
  · exact g_inj n n' h'
  · have := key n' n h'; omega

theorem A209861_surj : Function.Surjective A209861 := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, A209861_zero⟩
  have hL := (len_pos m hm).1
  set I := Ico (2 ^ (len m - 1)) (2 ^ len m)
  have hmaps : ∀ n ∈ I, A209861 n ∈ I := by
    intro n hn
    rw [mem_Ico] at hn ⊢
    have h1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn.1
    have hl := len_eq_of_bounds n _ hL hn.1 hn.2
    rw [A209861_eq n h1, hl]
    have := rk_lt n h1
    rw [hl] at this
    have hP : 2 ^ len m = 2 * 2 ^ (len m - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := I) (t := I)
    (fun n _ => A209861 n) hmaps (fun a b _ _ h => A209861_inj h) le_rfl
  obtain ⟨n, _, hn⟩ := hsurj m (mem_Ico.2 (len_bounds m hm))
  exact ⟨n, hn.symm⟩

/-- A209862: the inverse permutation of A209861. -/
noncomputable def A209862 (m : ℕ) : ℕ := Function.invFun A209861 m

theorem A209862_spec (m : ℕ) : A209861 (A209862 m) = m :=
  Function.rightInverse_invFun A209861_surj m

/-- Conjecture in A209861: A209861(A054429(n)) = A054429(A209861(n)) for n >= 1. -/
theorem A209861_conjecture (n : ℕ) (hn : 1 ≤ n) :
    A209861 (A054429 n) = A054429 (A209861 n) := A209861_conj n hn

/-- Conjecture in A209862: a(A054429(n)) = A054429(a(n)) for n >= 1. -/
theorem A209862_conjecture (m : ℕ) (hm : 1 ≤ m) :
    A209862 (A054429 m) = A054429 (A209862 m) := by
  set n := A209862 m with hn
  have h1 : A209861 n = m := A209862_spec m
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, A209861_zero] at h1; omega
    · exact h
  have := A209861_conj n hn1
  rw [h1] at this
  rw [← this]
  exact Function.leftInverse_invFun A209861_inj _

/-- Conjecture in A209860 (fixed points of A209861): for i >= 1, i is a fixed point iff
A054429(i) is one. -/
theorem A209860_conjecture (i : ℕ) (hi : 1 ≤ i) :
    A209861 i = i ↔ A209861 (A054429 i) = A054429 i := by
  rw [A209861_conj i hi]
  constructor
  · intro h; rw [h]
  · intro h
    have h1 : 1 ≤ A209861 i := by
      rw [A209861_eq i hi]; have : 1 ≤ 2 ^ (len i - 1) := Nat.one_le_two_pow; omega
    have := congrArg A054429 h
    rwa [(c_props _ h1).2.2, (c_props i hi).2.2] at this
