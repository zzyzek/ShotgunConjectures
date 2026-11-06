/-
OEIS A096127: a(n) is the largest k such that (n^2)!/(n!)^k is an integer (n >= 2).
Conjecture (entry text): a(n) = n+1 only when n is prime or a power of a prime.

Definition.
* `a n = Nat.findGreatest (fun k => n! ^ k ∣ (n^2)!) ((n^2)!)`. The bound
  (n^2)! is harmless: the predicate is downward closed and holds at n+1.

Main theorem.
* `A096127_eq_succ_iff`: for n ≥ 2, a n = n + 1 ↔ IsPrimePow n
  (the conjecture is the → direction; ← is the easy converse).

Route (s = base-p digit sum, Legendre: (p-1) v_p(m!) = m - s(m)).
* `s_add_le`: s(a+b) ≤ s(a) + s(b), from a! b! ∣ (a+b)!.
* `s_mul_le`: s(m n) ≤ s(m) s(n).
* `s_eq_one`: s(n) = 1 → n is a power of p.
* `ineq_two`: s(n) ≥ 2 → (n+2) v_p(n!) ≤ v_p((n^2)!), since
  (n+2)(n - s) ≤ n^2 - s^2 ≤ n^2 - s(n^2) when 2 ≤ s ≤ n.
* `ineq_one`: (n+1) v_p(n!) ≤ v_p((n^2)!) for n ≥ 1.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py, n = 2..5000 against the b-file).
-/
import Mathlib

open Nat

namespace A096127

/-- The sequence as the entry defines it. -/
def a (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => n ! ^ k ∣ (n ^ 2)!) ((n ^ 2)!)

/-- Base-p digit sum. -/
def s (p m : ℕ) : ℕ := (p.digits m).sum

lemma legendre (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (p - 1) * padicValNat p m ! = m - s p m :=
  sub_one_mul_padicValNat_factorial m

lemma s_le (p m : ℕ) : s p m ≤ m := digit_sum_le p m

lemma s_add_le (p : ℕ) [hp : Fact p.Prime] (a b : ℕ) : s p (a + b) ≤ s p a + s p b := by
  have h1 : a ! * b ! ∣ (a + b)! := factorial_mul_factorial_dvd_factorial_add a b
  have h2 : padicValNat p (a ! * b !) ≤ padicValNat p (a + b)! :=
    (padicValNat_dvd_iff_le (factorial_ne_zero _)).1
      (dvd_trans pow_padicValNat_dvd h1)
  rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)] at h2
  have e1 := legendre p a
  have e2 := legendre p b
  have e3 := legendre p (a + b)
  have l1 := s_le p a
  have l2 := s_le p b
  have l3 := s_le p (a + b)
  have h3 : (p - 1) * (padicValNat p a ! + padicValNat p b !) ≤
      (p - 1) * padicValNat p (a + b)! := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_add] at h3
  omega

lemma s_smul_le (p : ℕ) [Fact p.Prime] (k n : ℕ) : s p (k * n) ≤ k * s p n := by
  induction k with
  | zero => simp [s]
  | succ k ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact le_trans (s_add_le p _ _) (by omega)

lemma s_step (p : ℕ) [hp : Fact p.Prime] {m : ℕ} (hm : 0 < m) :
    s p m = m % p + s p (m / p) := by
  unfold s
  rw [digits_def' hp.out.one_lt hm]
  simp

lemma s_base_mul (p : ℕ) [hp : Fact p.Prime] (m : ℕ) : s p (p * m) = s p m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [s]
  · unfold s; rw [digits_base_mul hp.out.one_lt h]; simp

lemma s_mul_le (p : ℕ) [hp : Fact p.Prime] (m n : ℕ) : s p (m * n) ≤ s p m * s p n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [s]
    · have hpp : 0 < p := hp.out.pos
      have hlt : m / p < m := Nat.div_lt_self h hp.out.one_lt
      have hm : m * n = (m % p) * n + p * ((m / p) * n) := by
        have := Nat.mod_add_div m p
        calc m * n = (m % p + p * (m / p)) * n := by rw [this]
          _ = _ := by ring
      rw [hm, s_step p h]
      calc s p ((m % p) * n + p * ((m / p) * n))
          ≤ s p ((m % p) * n) + s p (p * ((m / p) * n)) := s_add_le p _ _
        _ = s p ((m % p) * n) + s p ((m / p) * n) := by rw [s_base_mul]
        _ ≤ (m % p) * s p n + s p (m / p) * s p n :=
            Nat.add_le_add (s_smul_le p _ _) (ih _ hlt)
        _ = (m % p + s p (m / p)) * s p n := by ring

lemma s_pos (p : ℕ) [hp : Fact p.Prime] {m : ℕ} (hm : 0 < m) : 1 ≤ s p m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [s_step p hm]
    by_cases h : m % p = 0
    · have h2 : 0 < m / p := by
        rcases Nat.eq_zero_or_pos (m / p) with h3 | h3
        · have := Nat.mod_add_div m p; rw [h, h3] at this; omega
        · exact h3
      have := ih _ (Nat.div_lt_self hm hp.out.one_lt) h2
      omega
    · omega

lemma s_eq_one (p : ℕ) [hp : Fact p.Prime] {m : ℕ} (hm : 0 < m) (h1 : s p m = 1) :
    ∃ k, m = p ^ k := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [s_step p hm] at h1
    have hd := Nat.mod_add_div m p
    rcases Nat.eq_zero_or_pos (m / p) with h3 | h3
    · refine ⟨0, ?_⟩
      have : s p (m / p) = 0 := by rw [h3]; simp [s]
      rw [h3] at hd; simp; omega
    · have := s_pos p h3
      have hmod : m % p = 0 := by omega
      obtain ⟨k, hk⟩ := ih _ (Nat.div_lt_self hm hp.out.one_lt) h3 (by omega)
      refine ⟨k + 1, ?_⟩
      rw [hmod, hk] at hd
      rw [pow_succ']; omega

lemma s_pow (p : ℕ) [hp : Fact p.Prime] (k : ℕ) : s p (p ^ k) = 1 := by
  induction k with
  | zero =>
    unfold s
    rw [pow_zero, digits_of_lt p 1 one_ne_zero hp.out.one_lt]; simp
  | succ k ih => rw [pow_succ, mul_comm, s_base_mul, ih]

/-- Divisibility of (n^2)! by (n!)^k, prime by prime. -/
lemma dvd_iff_val (n k : ℕ) :
    n ! ^ k ∣ (n ^ 2)! ↔
      ∀ p : ℕ, p.Prime → k * padicValNat p n ! ≤ padicValNat p (n ^ 2)! := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ (factorial_ne_zero _))
    (factorial_ne_zero _), Finsupp.le_def]
  constructor
  · intro h p hp
    have := h p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_def _ hp, Nat.factorization_def _ hp] at this
    exact this
  · intro h p
    by_cases hp : p.Prime
    · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      exact h p hp
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma val_ineq (p : ℕ) [hp : Fact p.Prime] {n c : ℕ}
    (key : (c + n) * (n - s p n) ≤ n ^ 2 - s p (n ^ 2)) :
    (n + c) * padicValNat p n ! ≤ padicValNat p (n ^ 2)! := by
  have e1 := legendre p n
  have e2 := legendre p (n ^ 2)
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  apply Nat.le_of_mul_le_mul_left _ hp1
  calc (p - 1) * ((n + c) * padicValNat p n !)
      = (n + c) * ((p - 1) * padicValNat p n !) := by ring
    _ = (c + n) * (n - s p n) := by rw [e1]; ring
    _ ≤ n ^ 2 - s p (n ^ 2) := key
    _ = (p - 1) * padicValNat p (n ^ 2)! := e2.symm

lemma ineq_c (p : ℕ) [hp : Fact p.Prime] {n c : ℕ} (hn : 1 ≤ n)
    (hs : c ≤ s p n) : (n + c) * padicValNat p n ! ≤ padicValNat p (n ^ 2)! := by
  apply val_ineq p
  have h1 : s p (n ^ 2) ≤ s p n * s p n := by rw [sq]; exact s_mul_le p n n
  have h2 := s_le p n
  have h3 := s_pos p hn
  set t := s p n
  -- (c+n)(n-t) ≤ n^2 - t^2 ≤ n^2 - s(n^2), using c ≤ t ≤ n
  have h4 : (c + n) * (n - t) ≤ n ^ 2 - t * t := by
    obtain ⟨d, hd⟩ : ∃ d, n = t + d := ⟨n - t, by omega⟩
    have hd' : n - t = d := by omega
    rw [hd']
    have hcd := Nat.mul_le_mul_right d hs
    have : (c + n) * d + t * t ≤ n ^ 2 := by rw [hd]; nlinarith
    omega
  have h5 : t * t ≤ n ^ 2 := by nlinarith
  omega

lemma ineq_one (n : ℕ) (hn : 1 ≤ n) : n ! ^ (n + 1) ∣ (n ^ 2)! := by
  rw [dvd_iff_val]
  intro p hp
  have := Fact.mk hp
  exact ineq_c p hn (s_pos p hn)

lemma ineq_two (n : ℕ) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n) : n ! ^ (n + 2) ∣ (n ^ 2)! := by
  rw [dvd_iff_val]
  intro p hp
  have := Fact.mk hp
  have hs : 2 ≤ s p n := by
    have := s_pos p (by omega : 0 < n)
    by_contra h
    have h1 : s p n = 1 := by omega
    obtain ⟨k, hk⟩ := s_eq_one p (by omega : 0 < n) h1
    apply hnp
    rw [isPrimePow_nat_iff]
    refine ⟨p, k, hp, ?_, hk.symm⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk; omega
    · exact h0
  exact ineq_c p (by omega) hs

lemma not_two (n : ℕ) (hn : 2 ≤ n) (hpp : IsPrimePow n) : ¬ n ! ^ (n + 2) ∣ (n ^ 2)! := by
  rw [dvd_iff_val]
  intro h
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
  have := Fact.mk hp
  have h1 := h p hp
  have e1 := legendre p (p ^ k)
  have e2 := legendre p ((p ^ k) ^ 2)
  rw [s_pow] at e1
  rw [← pow_mul, s_pow] at e2
  rw [← pow_mul] at h1
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have h2 := Nat.mul_le_mul_left (p - 1) h1
  set N := p ^ k
  have hN : (N : ℕ) ^ 2 = p ^ (k * 2) := by rw [← pow_mul]
  rw [← hN] at e2 h2
  have : (p - 1) * ((N + 2) * padicValNat p N !) = (N + 2) * (N - 1) := by
    rw [← e1]; ring
  rw [this, e2] at h2
  have : N ^ 2 - 1 < (N + 2) * (N - 1) := by
    obtain ⟨d, hd⟩ : ∃ d, N = d + 2 := ⟨N - 2, by omega⟩
    rw [hd]
    have e3 : d + 2 - 1 = d + 1 := by omega
    have e4 : (d + 2) ^ 2 - 1 = d * d + 4 * d + 3 := by ring_nf; omega
    rw [e3, e4]; nlinarith
  omega

lemma bound (n c : ℕ) (hn : 2 ≤ n) (hc : c ≤ 2) : n + c ≤ (n ^ 2)! := by
  have : n + c ≤ n ^ 2 := by nlinarith
  exact le_trans this (Nat.self_le_factorial _)

theorem A096127_eq_succ_iff (n : ℕ) (hn : 2 ≤ n) : a n = n + 1 ↔ IsPrimePow n := by
  unfold a
  constructor
  · intro h
    by_contra hpp
    have := Nat.le_findGreatest (P := fun k => n ! ^ k ∣ (n ^ 2)!) (bound n 2 hn le_rfl) (ineq_two n hn hpp)
    omega
  · intro hpp
    have hlo := Nat.le_findGreatest (P := fun k => n ! ^ k ∣ (n ^ 2)!) (bound n 1 hn (by norm_num)) (ineq_one n (by omega))
    have hspec := Nat.findGreatest_spec (P := fun k => n ! ^ k ∣ (n ^ 2)!) (bound n 1 hn (by norm_num)) (ineq_one n (by omega))
    apply le_antisymm _ hlo
    by_contra hgt
    rw [not_le] at hgt
    apply not_two n hn hpp
    exact dvd_trans (pow_dvd_pow _ hgt) hspec

/-- The conjecture as stated: a(n) = n+1 only for primes and prime powers. -/
theorem A096127_conjecture (n : ℕ) (hn : 2 ≤ n) (h : a n = n + 1) : IsPrimePow n :=
  (A096127_eq_succ_iff n hn).1 h

