import Mathlib

/-
NT-B40.3 (Mathlib). Guy B40 (Recamán): for every k, do the totatives of every sufficiently
large n contain a k-term arithmetic progression? README result: yes, for every fixed k.

Main theorem `B40_3_main`: for every k there is N such that for every n ≥ N there are a and
d > 0 with 1 ≤ a + j d < n and gcd(a + j d, n) = 1 for all j < k. (Explicitly
N = 2^(4·2^(8k) + 8).)

Proof (differs from the README's inclusion–exclusion sieve; a union bound suffices). Let
L = log₂ n, B = ⌊L/4⌋ and d = B# (primorial, d ≤ 4^B). Terms x_j = 1 + d(u + j) with
0 ≤ u < B are ≡ 1 modulo every prime ≤ B. A prime p > B dividing n does not divide d, and
since p > B > u, for each j at most one u < B has p ∣ x_j; so at most k·m values of u are bad,
m = number of prime factors of n above B. From (B+1)^m ≤ n < 2^(L+1) and log₂ B ≥ 8k one gets
k·m < B, so a good u exists; the terms are below 1 + 4^B (B + k) ≤ 2^L ≤ n.

Outside Lean: nothing.
-/

open Finset

theorem B40_3_main (k : ℕ) : ∃ N, ∀ n ≥ N, ∃ a d : ℕ, 0 < d ∧
    ∀ j < k, 1 ≤ a + j * d ∧ a + j * d < n ∧ Nat.Coprime (a + j * d) n := by
  refine ⟨2 ^ (4 * 2 ^ (8 * k) + 8), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn; exact absurd hn (Nat.not_le.2 (by positivity))
  set L := Nat.log 2 n with hLdef
  have hL : 4 * 2 ^ (8 * k) + 8 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have h2L : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hnL : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  set B := L / 4 with hBdef
  have hB : 2 ^ (8 * k) + 2 ≤ B := by omega
  have hkB : k ≤ B := by
    have := (Nat.lt_two_pow_self (n := 8 * k)).le
    omega
  set d := primorial B with hddef
  have hd_le : d ≤ 4 ^ B := primorial_le_four_pow B
  have hd_pos : 0 < d := primorial_pos B
  set S := n.primeFactors.filter fun p => B < p with hSdef
  -- The number m of prime factors of n above B satisfies k m < B.
  --
  have hm : k * #S < B := by
    set m := #S
    set b := Nat.log 2 B
    have hb : 8 * k ≤ b := Nat.le_log_of_pow_le (by norm_num) (by omega)
    have h2b : 2 ^ b ≤ B := Nat.pow_log_le_self 2 (by omega)
    have hprod : (B + 1) ^ m ≤ ∏ p ∈ S, p :=
      pow_card_le_prod S (fun p => p) (B + 1) (fun p hp => (mem_filter.1 hp).2)
    have hprodn : ∏ p ∈ S, p ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
        ((prod_dvd_prod_of_subset S n.primeFactors (fun p => p) (filter_subset _ _)).trans
          (Nat.prod_primeFactors_dvd n))
    have h1 : 2 ^ (b * m) < 2 ^ (L + 1) := by
      calc 2 ^ (b * m) = (2 ^ b) ^ m := by rw [pow_mul]
        _ ≤ (B + 1) ^ m := Nat.pow_le_pow_left (by omega) m
        _ ≤ n := hprod.trans hprodn
        _ < 2 ^ (L + 1) := hnL
    have h2 : b * m < L + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
    have h3 : 8 * (k * m) ≤ b * m := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right m hb
    omega
  -- A good u < B exists.
  --
  have hbad : #((range B).filter fun u => ∃ p ∈ S, ∃ j ∈ range k, p ∣ 1 + d * (u + j)) ≤
      #S * k := by
    calc #((range B).filter fun u => ∃ p ∈ S, ∃ j ∈ range k, p ∣ 1 + d * (u + j))
        ≤ #(S.biUnion fun p => (range k).biUnion fun j =>
            (range B).filter fun u => p ∣ 1 + d * (u + j)) := by
          apply card_le_card
          intro u hu
          simp only [mem_filter, mem_range] at hu
          obtain ⟨hu, p, hp, j, hj, hdiv⟩ := hu
          simp only [mem_biUnion, mem_filter, mem_range]
          exact ⟨p, hp, j, hj, hu, hdiv⟩
      _ ≤ ∑ p ∈ S, #((range k).biUnion fun j =>
            (range B).filter fun u => p ∣ 1 + d * (u + j)) := card_biUnion_le
      _ ≤ ∑ p ∈ S, ∑ j ∈ range k, #((range B).filter fun u => p ∣ 1 + d * (u + j)) :=
          sum_le_sum fun _ _ => card_biUnion_le
      _ ≤ ∑ p ∈ S, ∑ j ∈ range k, 1 := by
          apply sum_le_sum
          intro p hp
          apply sum_le_sum
          intro j _
          obtain ⟨hpn, hBp⟩ := mem_filter.1 hp
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpn
          have hpd : ¬p ∣ d := by
            rw [hddef, hpp.dvd_primorial_iff]; omega
          apply card_le_one.2
          intro u hu u' hu'
          simp only [mem_filter, mem_range] at hu hu'
          have key : ∀ x y, x < B → y < B → x ≤ y → p ∣ 1 + d * (x + j) →
              p ∣ 1 + d * (y + j) → x = y := by
            intro x y hx hy hxy h1 h2
            have : p ∣ d * (y - x) := by
              have := Nat.dvd_sub h2 h1
              rwa [show 1 + d * (y + j) - (1 + d * (x + j)) = d * (y - x) by
                rw [Nat.mul_sub]; ring_nf; omega] at this
            rcases (Nat.Prime.dvd_mul hpp).1 this with h | h
            · exact absurd h hpd
            · have := Nat.eq_zero_of_dvd_of_lt h (by omega)
              omega
          rcases le_total u u' with h | h
          · exact key u u' hu.1 hu'.1 h hu.2 hu'.2
          · exact (key u' u hu'.1 hu.1 h hu'.2 hu.2).symm
      _ = #S * k := by simp
  obtain ⟨u, hu, hgood⟩ : ∃ u ∈ range B,
      ¬∃ p ∈ S, ∃ j ∈ range k, p ∣ 1 + d * (u + j) := by
    by_contra hcon
    push Not at hcon
    have : (range B).filter (fun u => ∃ p ∈ S, ∃ j ∈ range k, p ∣ 1 + d * (u + j)) =
        range B := filter_true_of_mem fun u hu => by
      obtain ⟨p, hp, j, hj, h⟩ := hcon u hu
      exact ⟨p, hp, j, hj, h⟩
    rw [this, card_range] at hbad
    have : #S * k = k * #S := mul_comm _ _
    omega
  rw [mem_range] at hu
  -- The progression.
  --
  refine ⟨1 + d * u, d, hd_pos, fun j hj => ⟨by omega, ?_, ?_⟩⟩
  · have e : 1 + d * u + j * d = 1 + d * (u + j) := by ring
    rw [e]
    have hX : 2 * B + 1 ≤ 2 ^ (2 * B) := Nat.lt_two_pow_self
    have h4 : 4 ^ B = 2 ^ (2 * B) := by rw [pow_mul]; norm_num
    have hL4 : 2 ^ (2 * B) * 2 ^ (2 * B) ≤ 2 ^ L := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlt : d * (u + j) < 4 ^ B * (B + k) :=
      calc d * (u + j) < d * (B + k) := Nat.mul_lt_mul_of_pos_left (by omega) hd_pos
        _ ≤ 4 ^ B * (B + k) := Nat.mul_le_mul_right _ hd_le
    rw [h4] at hlt
    have : 2 ^ (2 * B) * (B + k) + 1 ≤ 2 ^ (2 * B) * 2 ^ (2 * B) := by
      have : B + k + 1 ≤ 2 ^ (2 * B) := by omega
      nlinarith
    omega
  · have e : 1 + d * u + j * d = 1 + d * (u + j) := by ring
    rw [e]
    apply Nat.coprime_of_dvd
    intro p hp hpx hpn
    by_cases hpB : p ≤ B
    · have hpd : p ∣ d := by rw [hddef, hp.dvd_primorial_iff]; exact hpB
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hpd _)).1 (by rwa [add_comm] at hpx)
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    · apply hgood
      refine ⟨p, ?_, j, mem_range.2 hj, hpx⟩
      rw [mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, hpn, hn0⟩, by omega⟩
