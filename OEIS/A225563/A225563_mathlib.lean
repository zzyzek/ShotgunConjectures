import Mathlib

/-
OEIS A225563: numbers whose totient-trajectory (m, phi m, phi (phi m), ..., 1)
can be partitioned into two sets with the same sum.
Conjecture (entry): no totient-trajectory can be partitioned into an odd
number of sets with the same sum.

Definitions.  `traj n` is the list n, phi n, phi (phi n), ..., 1 (for n >= 1;
it stops at the first value <= 1).  A partition into k parts of equal sum s
is a list `parts` of k lists whose concatenation is a permutation of
`traj n` and each of whose members sums to s (parts may be empty, which only
makes the statement stronger; the trajectory has distinct entries, so this
covers partitions into sets).

Main theorem.
* `A225563_no_partition`: for n >= 1 and k >= 3 there is no such partition.
  In particular none for odd k >= 3, which is the conjecture (k = 1 is the
  trivial one-part partition).

Route.
* `two_mul_totient_le`: 2 * phi n <= n for even n.
* `traj_sum_even`: for m = 1 or m even, sum (traj m) <= 2m - 1.
* `traj_sum_lt`: for n >= 1, sum (traj n) < 3n.
* A part containing n has sum >= n, so k * s >= 3n > sum (traj n) = k * s.

Checked: everything above.  Not checked: nothing beyond reading the entry.
-/

open Nat

def traj (n : ℕ) : List ℕ :=
  if n ≤ 1 then [n] else n :: traj (Nat.totient n)
termination_by n
decreasing_by exact Nat.totient_lt n (by omega)

lemma traj_of_le {n : ℕ} (h : n ≤ 1) : traj n = [n] := by
  rw [traj]; simp [h]

lemma traj_of_gt {n : ℕ} (h : 1 < n) : traj n = n :: traj (Nat.totient n) := by
  rw [traj]; simp [show ¬ n ≤ 1 by omega]

lemma two_mul_totient_le (n : ℕ) (h : 2 ∣ n) : 2 * Nat.totient n ≤ n := by
  have hc : Nat.totient n ≤ n / 2 := by
    rw [Nat.totient]
    have hodd : ∀ a, n.Coprime a → a % 2 = 1 := by
      intro a ha
      by_contra hne
      have h2 : 2 ∣ a := by omega
      have := Nat.dvd_gcd h h2
      rw [ha] at this
      omega
    calc (Finset.filter (fun a => n.Coprime a) (Finset.range n)).card
        ≤ (Finset.range (n / 2)).card := by
          apply Finset.card_le_card_of_injOn (fun a => a / 2)
          · intro a ha
            simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
            have := hodd a ha.2
            simp only [Finset.coe_range, Set.mem_Iio]
            omega
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
            have h1 := hodd a ha.2
            have h2 := hodd b hb.2
            simp only at hab
            omega
      _ = n / 2 := Finset.card_range _
  omega

/-- phi m is 1 or even, for m >= 2. -/
lemma totient_one_or_even (m : ℕ) (hm : 2 ≤ m) :
    Nat.totient m = 1 ∨ 2 ∣ Nat.totient m := by
  rcases Nat.lt_or_ge 2 m with h | h
  · right; exact even_iff_two_dvd.mp (Nat.totient_even h)
  · left; have : m = 2 := by omega
    subst this; decide

lemma traj_sum_even : ∀ m : ℕ, 1 ≤ m → (m = 1 ∨ 2 ∣ m) → (traj m).sum ≤ 2 * m - 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm1 hm
    rcases Nat.lt_or_ge 1 m with hgt | hle
    · rw [traj_of_gt hgt, List.sum_cons]
      have hpos : 1 ≤ Nat.totient m := Nat.totient_pos.mpr (by omega)
      have hlt : Nat.totient m < m := Nat.totient_lt m hgt
      have hev : 2 ∣ m := by rcases hm with h | h <;> omega
      have h2 := two_mul_totient_le m hev
      have := ih (Nat.totient m) hlt hpos (totient_one_or_even m (by omega))
      omega
    · rw [traj_of_le hle]
      simp
      omega

lemma traj_sum_lt (n : ℕ) (hn : 1 ≤ n) : (traj n).sum < 3 * n := by
  rcases Nat.lt_or_ge 1 n with hgt | hle
  · rw [traj_of_gt hgt, List.sum_cons]
    have hpos : 1 ≤ Nat.totient n := Nat.totient_pos.mpr (by omega)
    have hlt : Nat.totient n < n := Nat.totient_lt n hgt
    have := traj_sum_even (Nat.totient n) hpos (totient_one_or_even n (by omega))
    omega
  · rw [traj_of_le hle]
    simp
    omega

lemma flatten_sum_const (s : ℕ) :
    ∀ parts : List (List ℕ), (∀ p ∈ parts, p.sum = s) →
      parts.flatten.sum = parts.length * s := by
  intro parts
  induction parts with
  | nil => intro _; simp
  | cons p ps ih =>
    intro h
    rw [List.flatten_cons, List.sum_append, h p (by simp),
      ih (fun q hq => h q (by simp [hq])), List.length_cons]
    ring

lemma mem_traj_self (n : ℕ) : n ∈ traj n := by
  rcases Nat.lt_or_ge 1 n with hgt | hle
  · rw [traj_of_gt hgt]; simp
  · rw [traj_of_le hle]; simp

theorem A225563_no_partition (n k s : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k)
    (parts : List (List ℕ)) (hlen : parts.length = k)
    (hperm : parts.flatten.Perm (traj n)) (hsum : ∀ p ∈ parts, p.sum = s) :
    False := by
  have htot : (traj n).sum = k * s := by
    rw [← hperm.sum_eq, flatten_sum_const s parts hsum, hlen]
  have hmem : n ∈ parts.flatten := hperm.mem_iff.mpr (mem_traj_self n)
  obtain ⟨p, hp, hnp⟩ := List.mem_flatten.mp hmem
  have hns : n ≤ s := by
    rw [← hsum p hp]
    exact List.le_sum_of_mem hnp
  have hlt := traj_sum_lt n hn
  have : 3 * n ≤ k * s := Nat.mul_le_mul hk hns
  omega

/-- The conjecture as stated: no partition into an odd number k > 1 of parts. -/
theorem A225563_conjecture (n k s : ℕ) (hn : 1 ≤ n) (hodd : k % 2 = 1) (hk : k ≠ 1)
    (parts : List (List ℕ)) (hlen : parts.length = k)
    (hperm : parts.flatten.Perm (traj n)) (hsum : ∀ p ∈ parts, p.sum = s) :
    False :=
  A225563_no_partition n k s hn (by omega) parts hlen hperm hsum
