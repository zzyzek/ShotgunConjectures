/-
OEIS A221650, Mathlib proof.

A221650: tetrahedron P(n, j, k) = T(j, k)·p(n - j) with T(j, k) = 1 if
k ∣ j, else 0, and p = the partition numbers. Conjectures (O. Omar, 2013):
(1) P(n, j, k) is the number of partitions of n that contain at least m
parts of size k, m = j/k, if k ∣ j; otherwise P(n, j, k) = 0.
(2) P(n, j, k) is the number of parts that are the m-th part of size k,
over all partitions of n.

Definitions: partitions are Mathlib's `Nat.Partition n`; p(r) =
`Fintype.card (Nat.Partition r)`; `A221650_P n j k` = [k ∣ j]·p(n - j).
For (2), the parts of size k of a partition π, listed in order, are the 1st,
..., (count k π)-th part of size k; the number of them that are the m-th is
#{i ∈ [1, count k π] : i = m}.

Main theorem `A221650_main`: for all 1 ≤ k ≤ j ≤ n,
* if k ∣ j: P(n, j, k) = #{π ⊢ n : count k π ≥ j/k}, and
  P(n, j, k) = Σ_{π ⊢ n} #{i ∈ [1, count k π] : i = j/k};
* if k ∤ j: P(n, j, k) = 0.
This is the README result. Proof: removing j/k copies of k is a bijection
onto the partitions of n - j. Nothing is outside Lean.
-/
import Mathlib

/-- P(n, j, k) = T(j, k)·p(n - j). -/
def A221650_P (n j k : ℕ) : ℕ :=
  if k ∣ j then Fintype.card (Nat.Partition (n - j)) else 0

/-- Adding m parts equal to k (k ≥ 1) to a partition of n - m k. -/
def A221650_add (n m k : ℕ) (hk : 0 < k) (h : m * k ≤ n) (q : Nat.Partition (n - m * k)) :
    Nat.Partition n where
  parts := q.parts + Multiset.replicate m k
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.1 hi with hi | hi
    · exact q.parts_pos hi
    · rw [Multiset.eq_of_mem_replicate hi]; exact hk
  parts_sum := by
    rw [Multiset.sum_add, q.parts_sum, Multiset.sum_replicate, smul_eq_mul]
    omega

theorem A221650_count (n m k : ℕ) (hk : 0 < k) (h : m * k ≤ n) :
    Fintype.card (Nat.Partition (n - m * k)) =
      (Finset.univ.filter (fun π : Nat.Partition n => m ≤ π.parts.count k)).card := by
  rw [← Finset.card_univ]
  apply Finset.card_bij (fun q _ => A221650_add n m k hk h q)
  · intro q _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, A221650_add, Multiset.count_add,
      Multiset.count_replicate_self]
    omega
  · intro q _ q' _ he
    have := congrArg Nat.Partition.parts he
    simp only [A221650_add] at this
    exact Nat.Partition.ext (add_right_cancel this)
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    have hle : Multiset.replicate m k ≤ π.parts := Multiset.le_count_iff_replicate_le.1 hπ
    refine ⟨⟨π.parts - Multiset.replicate m k, fun hi => π.parts_pos (Multiset.mem_of_le
      (Multiset.sub_le_self _ _) hi), ?_⟩, Finset.mem_univ _, ?_⟩
    · have := congrArg Multiset.sum (tsub_add_cancel_of_le hle)
      rw [Multiset.sum_add, π.parts_sum, Multiset.sum_replicate, smul_eq_mul] at this
      omega
    · apply Nat.Partition.ext
      simp only [A221650_add]
      exact tsub_add_cancel_of_le hle

theorem A221650_main (n j k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) (hjn : j ≤ n) :
    (k ∣ j →
      A221650_P n j k =
        (Finset.univ.filter (fun π : Nat.Partition n => j / k ≤ π.parts.count k)).card ∧
      A221650_P n j k = ∑ π : Nat.Partition n,
        ((Finset.Icc 1 (π.parts.count k)).filter (fun i => i = j / k)).card) ∧
    (¬ k ∣ j → A221650_P n j k = 0) := by
  refine ⟨fun hd => ?_, fun hd => by simp [A221650_P, hd]⟩
  obtain ⟨m, rfl⟩ := hd
  have hm : k * m / k = m := Nat.mul_div_cancel_left m (by omega)
  have h1 : A221650_P n (k * m) k =
      (Finset.univ.filter (fun π : Nat.Partition n => m ≤ π.parts.count k)).card := by
    simp only [A221650_P, dvd_mul_right, ite_true]
    rw [← A221650_count n m k (by omega) (by linarith), Nat.mul_comm]
  rw [hm]
  refine ⟨h1, h1.trans ?_⟩
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; omega
    · exact h0
  split_ifs with h
  · symm
    rw [Finset.card_eq_one]
    exact ⟨m, by ext i; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega⟩
  · symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
