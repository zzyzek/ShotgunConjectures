/-
OEIS A109926: least k such that k - 2^r is prime for exactly n values of r
(r ≥ 0).  Conjecture (R. G. Wilson v, 2005, in the entry):
"a(n+15) == 0 (mod 30) for n > 4".

Definitions.
* `reps k` = #{r : 2^r < k ∧ Nat.Prime (k - 2^r)} (r ranges over `range k`,
  which contains every r with 2^r < k).
* The entry's a(n) is the least k with `reps k = n` (`IsLeast`).

Main theorems.
* `odd_of_three_le`: every k with reps k ≥ 3 is odd (an even k has
  k - 2^r even for r ≥ 1, prime only when k = 2^r + 2, one r at most).
* `A109926_not_dvd_30`: for m ≥ 3 the least k with reps k = m (whenever it
  exists) is not divisible by 30.  So the conjecture as printed fails at
  every index n + 15 ≥ 20 where a(n+15) exists, e.g. a(20) = 2282745465
  (entry data; certificate/a20.gp checks reps = 20).

Not checked in this file: existence and value of a(20) (minimality is from
the entry, D. Johnson 2009; reps(2282745465) = 20 by PARI in certificate/).
-/
import Mathlib

namespace A109926

def repSet (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun r => 2 ^ r < k ∧ Nat.Prime (k - 2 ^ r)

def reps (k : ℕ) : ℕ := (repSet k).card

lemma mem_repSet {k r : ℕ} : r ∈ repSet k ↔ 2 ^ r < k ∧ Nat.Prime (k - 2 ^ r) := by
  unfold repSet
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨lt_of_lt_of_le (Nat.lt_two_pow_self) h.1.le, h⟩

theorem odd_of_three_le (k : ℕ) (hk : 3 ≤ reps k) : k % 2 = 1 := by
  by_contra hev
  have he : k % 2 = 0 := by omega
  -- the elements r ≥ 1 of repSet k satisfy 2^r = k - 2
  have key : ∀ r ∈ repSet k, 1 ≤ r → 2 ^ r + 2 = k := by
    intro r hr h1
    rw [mem_repSet] at hr
    obtain ⟨hlt, hp⟩ := hr
    have h2 : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)
    have h3 : 2 ∣ k - 2 ^ r := by
      apply Nat.dvd_sub (Nat.dvd_of_mod_eq_zero he) h2
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h3).resolve_left (by norm_num)
    omega
  have hcard1 : ((repSet k).filter (fun r => 1 ≤ r)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have := (key a ha.1 ha.2).trans (key b hb.1 hb.2).symm
    exact Nat.pow_right_injective (le_refl 2) (by simp only; omega)
  have hcard0 : ((repSet k).filter (fun r => ¬ 1 ≤ r)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    omega
  have := Finset.card_filter_add_card_filter_not (s := repSet k) (fun r => 1 ≤ r)
  unfold reps at hk
  omega

theorem A109926_not_dvd_30 (m : ℕ) (hm : 3 ≤ m) (k : ℕ)
    (hk : IsLeast {k | reps k = m} k) : ¬ 30 ∣ k := by
  have := odd_of_three_le k (by rw [hk.1]; exact hm)
  omega
