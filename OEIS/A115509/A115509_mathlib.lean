/-
OEIS A115509, Mathlib proof of the formula
"If 2^(k+1) <= n < 3*2^k for k >= 1, then a(n) = 0."

A115509(n) (offset 1): number of circular permutations of {1, ..., n} such that in every
pair of adjacent elements each element in binary has ones at the same or adjacent
positions to those of the other element.

Formalisation.
- `near x y`: every 1-bit of x (position i) has a 1-bit of y at position i-1, i or i+1.
- `good x y := near x y ∧ near y x` (the adjacency condition of the entry).
- `cyclicGood l`: consecutive entries of the list l are good, and so are its last and
  first entries (the arrangement is read around a circle).
- `arrangements n`: the lists that are permutations of [1, ..., n], start with 1 and
  satisfy `cyclicGood`. Fixing the first entry to 1 picks one representative per
  rotation class, so `A115509 n := (arrangements n).card` counts circular permutations
  (mirror images counted separately, as the data a(3) = 2 requires).

Main theorems.
- `A115509_no_cycle`: for k ≥ 1 and 2^(k+1) ≤ n < 3·2^k, no permutation of [1, ..., n]
  (with any first entry) satisfies `cyclicGood`.
- `A115509_formula`: under the same hypotheses, A115509 n = 0.
Argument: a neighbour y ≤ n of 2^(k+1) has all its 1-bits at positions ≥ k, so 2^k ∣ y,
and y < 3·2^k forces y ∈ {2^k, 2^(k+1)}; the two neighbours of 2^(k+1) on a circle of
n ≥ 4 distinct numbers are distinct and differ from 2^(k+1).

Not checked in Lean: the listed terms of the entry (certificate/check_A115509.py
recomputes them from the same definition).
-/
import Mathlib

open Classical

/-- Every 1-bit of `x` has a 1-bit of `y` at the same or an adjacent position. -/
def near (x y : ℕ) : Prop :=
  ∀ i, x.testBit i = true → ∃ j, y.testBit j = true ∧ (j = i ∨ j + 1 = i ∨ j = i + 1)

/-- The adjacency condition of A115509. -/
def good (x y : ℕ) : Prop := near x y ∧ near y x

/-- All cyclically adjacent pairs of `l` are good. -/
def cyclicGood (l : List ℕ) : Prop :=
  (∀ i (h : i + 1 < l.length), good l[i] l[i + 1]) ∧
    (∀ h : 0 < l.length, good l[l.length - 1] l[0])

/-- Circular arrangements of 1..n, normalised to start with 1. -/
noncomputable def arrangements (n : ℕ) : Finset (List ℕ) :=
  (List.range' 1 n).permutations.toFinset.filter (fun l => l.head? = some 1 ∧ cyclicGood l)

/-- A115509(n): number of circular arrangements. -/
noncomputable def A115509 (n : ℕ) : ℕ := (arrangements n).card

/-- A number y with 1 ≤ y < 3·2^k whose 1-bits are all next to the 1-bit of 2^(k+1)
is 2^k or 2^(k+1). -/
theorem neighbour_eq {k y : ℕ} (hy1 : 1 ≤ y) (hy2 : y < 3 * 2 ^ k)
    (h : near y (2 ^ (k + 1))) : y = 2 ^ k ∨ y = 2 ^ (k + 1) := by
  have hmod : y % 2 ^ k = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < k
    · cases hb : y.testBit i
      · simp
      · obtain ⟨j, hj, hji⟩ := h i hb
        rw [Nat.testBit_two_pow] at hj
        have : k + 1 = j := of_decide_eq_true hj
        omega
    · simp [hi]
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod
  have h' : 2 ^ k * c < 2 ^ k * 3 := by rw [← hc, mul_comm]; exact hy2
  have hc3 : c < 3 := Nat.lt_of_mul_lt_mul_left h'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    omega
  rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
  · left
    rw [hc, mul_one]
  · right
    rw [hc, pow_succ]

/-- No cyclic arrangement exists when 2^(k+1) ≤ n < 3·2^k, k ≥ 1. -/
theorem A115509_no_cycle {k n : ℕ} (hk : 1 ≤ k) (h1 : 2 ^ (k + 1) ≤ n) (h2 : n < 3 * 2 ^ k)
    (l : List ℕ) (hl : l.Perm (List.range' 1 n)) : ¬ cyclicGood l := by
  rintro ⟨hc, hlast⟩
  have hnd : l.Nodup := hl.nodup_iff.mpr List.nodup_range'
  have hlen : l.length = n := by rw [hl.length_eq, List.length_range']
  have h4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  -- Entries lie in 1..n.
  have hbound : ∀ p (hp : p < l.length), 1 ≤ l[p] ∧ l[p] < 3 * 2 ^ k := by
    intro p hp
    have hm : l[p] ∈ List.range' 1 n := hl.mem_iff.mp (List.getElem_mem hp)
    rw [List.mem_range'_1] at hm
    omega
  -- 2^(k+1) occurs at some index i.
  have hmem : 2 ^ (k + 1) ∈ l := by
    rw [hl.mem_iff, List.mem_range'_1]
    omega
  obtain ⟨i, hi, hli⟩ := List.getElem_of_mem hmem
  -- Any neighbour (index p ≠ i) of 2^(k+1) is 2^k.
  have hnb : ∀ p (hp : p < l.length), p ≠ i → near l[p] (2 ^ (k + 1)) → l[p] = 2 ^ k := by
    intro p hp hpi hnear
    rcases neighbour_eq (hbound p hp).1 (hbound p hp).2 hnear with h | h
    · exact h
    · exact absurd ((hnd.getElem_inj_iff).mp (h.trans hli.symm)) hpi
  -- Two distinct neighbour indices give a contradiction.
  have hfin : ∀ p q (hp : p < l.length) (hq : q < l.length), p ≠ q → p ≠ i → q ≠ i →
      near l[p] (2 ^ (k + 1)) → near l[q] (2 ^ (k + 1)) → False := by
    intro p q hp hq hpq hpi hqi np nq
    have e : l[p] = l[q] := (hnb p hp hpi np).trans (hnb q hq hqi nq).symm
    exact hpq ((hnd.getElem_inj_iff).mp e)
  have hL : 4 ≤ l.length := by omega
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · -- i = 0: neighbours at 1 and length - 1.
    subst h0
    have g1 := hc 0 (by omega)
    have g2 := hlast (by omega)
    simp only [Nat.zero_add] at g1
    rw [hli] at g1 g2
    exact hfin 1 (l.length - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      g1.2 g2.1
  · by_cases hend : i + 1 < l.length
    · -- interior: neighbours at i - 1 and i + 1.
      have g1 := hc i hend
      have g2 := hc (i - 1) (by omega)
      have e : i - 1 + 1 = i := by omega
      simp only [e] at g2
      rw [hli] at g1 g2
      exact hfin (i + 1) (i - 1) hend (by omega) (by omega) (by omega) (by omega) g1.2 g2.1
    · -- i = length - 1: neighbours at i - 1 and 0.
      have hie : i = l.length - 1 := by omega
      have g1 := hlast (by omega)
      have g2 := hc (i - 1) (by omega)
      have e : i - 1 + 1 = i := by omega
      simp only [e] at g2
      simp only [← hie] at g1
      rw [hli] at g1 g2
      exact hfin 0 (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega) g1.2 g2.1

/-- The OEIS formula: a(n) = 0 when 2^(k+1) ≤ n < 3·2^k, k ≥ 1. -/
theorem A115509_formula {k n : ℕ} (hk : 1 ≤ k) (h1 : 2 ^ (k + 1) ≤ n) (h2 : n < 3 * 2 ^ k) :
    A115509 n = 0 := by
  unfold A115509 arrangements
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl ⟨_, hg⟩
  rw [List.mem_toFinset, List.mem_permutations] at hl
  exact A115509_no_cycle hk h1 h2 l hl hg

