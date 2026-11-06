/-
OEIS A227345: partitions of n into distinct parts by boundary size.

The boundary size of a partition into distinct parts is the number of parts p
such that not both p-1 and p+1 are parts.  T n k is the number of partitions of
n into distinct parts with boundary size k, i.e. the number of subsets S of
{1, ..., n} with sum n and boundary size k (the entry's definition).

Checked here: Devlin's conjecture (Jul 13 2013), for n >= 1,
  T n k > 0  <->  0 < k  and  3 k^2 <= 4 n
(the entry writes 0 < k^2 * 3/4 <= n).
Proof: the boundary parts contain no three consecutive integers, which forces
4 * (their sum) >= 3 k^2; conversely pairs {3j+1, 3j+2} plus a top pair or a
top singleton give every n >= 3k^2/4.
Not checked here: agreement of T with the entry's data (certificate/check.py).
-/
import Mathlib

namespace A227345

open Finset

/-- Boundary size: number of parts p such that not both p-1 and p+1 are parts. -/
def bdry (S : Finset ℕ) : ℕ := (S.filter (fun p => ¬ (p - 1 ∈ S ∧ p + 1 ∈ S))).card

/-- A227345(n, k): partitions of n into distinct parts with boundary size k. -/
def T (n k : ℕ) : ℕ :=
  ((Icc 1 n).powerset.filter (fun S => S.sum id = n ∧ bdry S = k)).card

theorem T_pos_iff (n k : ℕ) :
    0 < T n k ↔ ∃ S : Finset ℕ, 0 ∉ S ∧ S.sum id = n ∧ bdry S = k := by
  unfold T
  rw [card_pos]
  constructor
  · rintro ⟨S, hS⟩
    rw [mem_filter, mem_powerset] at hS
    refine ⟨S, fun h0 => ?_, hS.2.1, hS.2.2⟩
    have := mem_Icc.1 (hS.1 h0)
    omega
  · rintro ⟨S, h0, hs, hb⟩
    refine ⟨S, ?_⟩
    rw [mem_filter, mem_powerset]
    refine ⟨fun p hp => ?_, hs, hb⟩
    have hle : p ≤ S.sum id := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hp
    rw [hs] at hle
    have hp0 : p ≠ 0 := fun h => h0 (h ▸ hp)
    rw [mem_Icc]
    omega

/-- Boundary size is additive across a gap at a. -/
theorem bdry_union (S U : Finset ℕ) (a : ℕ) (hS : ∀ x ∈ S, x < a) (hU : ∀ x ∈ U, a < x) :
    bdry (S ∪ U) = bdry S + bdry U := by
  unfold bdry
  have hdis : Disjoint (S.filter (fun p => ¬ (p - 1 ∈ S ∧ p + 1 ∈ S)))
      (U.filter (fun p => ¬ (p - 1 ∈ U ∧ p + 1 ∈ U))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := hS x (mem_filter.1 hx).1
    have := hU x (mem_filter.1 hx').1
    omega
  rw [← card_union_of_disjoint hdis]
  congr 1
  ext p
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨hp | hp, h⟩
    · exact Or.inl ⟨hp, fun ⟨h1, h2⟩ => h ⟨Or.inl h1, Or.inl h2⟩⟩
    · exact Or.inr ⟨hp, fun ⟨h1, h2⟩ => h ⟨Or.inr h1, Or.inr h2⟩⟩
  · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
    · refine ⟨Or.inl hp, ?_⟩
      rintro ⟨h1 | h1, h2 | h2⟩
      · exact h ⟨h1, h2⟩
      · have := hS p hp; have := hU _ h2; omega
      · have := hS p hp; have := hU _ h1; omega
      · have := hS p hp; have := hU _ h2; omega
    · refine ⟨Or.inr hp, ?_⟩
      rintro ⟨h1 | h1, h2 | h2⟩
      · have := hU p hp; have := hS _ h1; omega
      · have := hU p hp; have := hS _ h1; omega
      · have := hU p hp; have := hS _ h2; omega
      · exact h ⟨h1, h2⟩

theorem bdry_pair (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) : bdry {a, b} = 2 := by
  unfold bdry
  rw [filter_true_of_mem, card_pair (by omega)]
  intro p hp
  simp only [mem_insert, mem_singleton] at hp ⊢
  omega

theorem bdry_single (c : ℕ) : bdry {c} = 1 := by
  unfold bdry
  rw [filter_true_of_mem, card_singleton]
  intro p hp
  simp only [mem_singleton] at hp ⊢
  omega

/-- The pairs {3j+1, 3j+2}, j < m. -/
def A : ℕ → Finset ℕ
  | 0 => ∅
  | m + 1 => A m ∪ {3 * m + 1, 3 * m + 2}

theorem A_mem (m : ℕ) : ∀ x ∈ A m, 1 ≤ x ∧ x < 3 * m := by
  induction m with
  | zero => simp [A]
  | succ m ih =>
    intro x hx
    simp only [A, mem_union, mem_insert, mem_singleton] at hx
    rcases hx with hx | hx
    · have := ih x hx; omega
    · omega

theorem A_sum (m : ℕ) : (A m).sum id = 3 * m ^ 2 := by
  induction m with
  | zero => simp [A]
  | succ m ih =>
    have hdis : Disjoint (A m) {3 * m + 1, 3 * m + 2} := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have := A_mem m x hx
      simp only [mem_insert, mem_singleton] at hx'
      omega
    simp only [A]
    rw [sum_union hdis, ih, sum_pair (by omega)]
    simp only [id]
    ring

theorem A_bdry (m : ℕ) : bdry (A m) = 2 * m := by
  induction m with
  | zero => simp [A, bdry]
  | succ m ih =>
    simp only [A]
    rw [bdry_union _ _ (3 * m) (fun x hx => (A_mem m x hx).2) (by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      omega), ih, bdry_pair _ _ (by omega) (by omega)]
    ring

/-- Existence: every n with 3k^2 <= 4n has a distinct-part partition with boundary k. -/
theorem exists_of_le (n k : ℕ) (hk : 0 < k) (h : 3 * k ^ 2 ≤ 4 * n) :
    ∃ S : Finset ℕ, 0 ∉ S ∧ S.sum id = n ∧ bdry S = k := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hsq : 3 * (2 * (m + 1)) ^ 2 = 12 * m ^ 2 + 24 * m + 12 := by ring
    set b := n - 3 * m ^ 2 - (3 * m + 1) with hb
    have hb' : 3 * m + 1 < b := by omega
    have hU : ∀ x ∈ ({3 * m + 1, b} : Finset ℕ), 3 * m < x := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      omega
    have hdis : Disjoint (A m) {3 * m + 1, b} := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have := A_mem m x hx
      have := hU x hx'
      omega
    refine ⟨A m ∪ {3 * m + 1, b}, ?_, ?_, ?_⟩
    · intro h0
      rcases mem_union.1 h0 with h0 | h0
      · have := A_mem m 0 h0; omega
      · have := hU 0 h0; omega
    · rw [sum_union hdis, A_sum, sum_pair (by omega)]
      simp only [id]
      omega
    · rw [bdry_union _ _ (3 * m) (fun x hx => (A_mem m x hx).2) hU, A_bdry,
        bdry_pair _ _ (by omega) hb']
      ring
  · have hsq : 3 * (2 * m + 1) ^ 2 = 12 * m ^ 2 + 12 * m + 3 := by ring
    set c := n - 3 * m ^ 2 with hc
    have hc' : 3 * m < c := by omega
    have hU : ∀ x ∈ ({c} : Finset ℕ), 3 * m < x := by
      intro x hx
      rw [mem_singleton] at hx
      omega
    have hdis : Disjoint (A m) {c} := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have := A_mem m x hx
      have := hU x hx'
      omega
    refine ⟨A m ∪ {c}, ?_, ?_, ?_⟩
    · intro h0
      rcases mem_union.1 h0 with h0 | h0
      · have := A_mem m 0 h0; omega
      · have := hU 0 h0; omega
    · rw [sum_union hdis, A_sum, sum_singleton]
      simp only [id]
      omega
    · rw [bdry_union _ _ (3 * m) (fun x hx => (A_mem m x hx).2) hU, A_bdry, bdry_single]

/-- No three consecutive integers. -/
def NoThree (B : Finset ℕ) : Prop := ∀ x, ¬ (x ∈ B ∧ x + 1 ∈ B ∧ x + 2 ∈ B)

theorem NoThree.mono {B C : Finset ℕ} (h : NoThree C) (hBC : B ⊆ C) : NoThree B :=
  fun x ⟨h1, h2, h3⟩ => h x ⟨hBC h1, hBC h2, hBC h3⟩

/-- A subset of {1, ..., M} without three consecutive integers has at most (2M+2)/3 elements. -/
theorem card_le (M : ℕ) : ∀ B : Finset ℕ, (∀ x ∈ B, 1 ≤ x ∧ x ≤ M) → NoThree B →
    3 * B.card ≤ 2 * M + 2 := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro B hB hN
    by_cases hM : M ≤ 2
    · have hsub : B ⊆ Icc 1 M := fun x hx => mem_Icc.2 (hB x hx)
      have := card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    · have hsplit := card_filter_add_card_filter_not (s := B) (fun x => x ≤ M - 3)
      have h1 : 3 * (B.filter (fun x => x ≤ M - 3)).card ≤ 2 * (M - 3) + 2 :=
        ih (M - 3) (by omega) _ (fun x hx => by
          rw [mem_filter] at hx
          exact ⟨(hB x hx.1).1, hx.2⟩) (hN.mono (filter_subset _ _))
      have h2 : (B.filter (fun x => ¬ x ≤ M - 3)).card ≤ 2 := by
        have hsub : B.filter (fun x => ¬ x ≤ M - 3) ⊆ {M - 2, M - 1, M} := by
          intro x hx
          rw [mem_filter] at hx
          have := hB x hx.1
          simp only [mem_insert, mem_singleton]
          omega
        by_contra hc
        have h3 : ({M - 2, M - 1, M} : Finset ℕ).card ≤ 3 := card_le_three
        have heq := eq_of_subset_of_card_le hsub (by omega)
        have hm : ∀ y ∈ ({M - 2, M - 1, M} : Finset ℕ), y ∈ B := by
          intro y hy
          rw [← heq] at hy
          exact (mem_filter.1 hy).1
        apply hN (M - 2)
        refine ⟨hm _ (by simp), ?_, ?_⟩
        · have : M - 2 + 1 = M - 1 := by omega
          rw [this]; exact hm _ (by simp)
        · have : M - 2 + 2 = M := by omega
          rw [this]; exact hm _ (by simp)
      omega

/-- Sum bound for sets of positive integers without three consecutive integers. -/
theorem sum_bound (B : Finset ℕ) (hpos : ∀ x ∈ B, 1 ≤ x) (hN : NoThree B) :
    3 * B.card ^ 2 + B.card % 2 ≤ 4 * B.sum id := by
  induction B using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hc := card_le a (insert a s) (fun x hx => by
      rcases mem_insert.1 hx with rfl | hx
      · exact ⟨hpos x (mem_insert_self _ _), le_refl _⟩
      · exact ⟨hpos x (mem_insert_of_mem hx), (hlt x hx).le⟩) hN
    have ih' := ih (fun x hx => hpos x (mem_insert_of_mem hx)) (hN.mono (subset_insert _ _))
    rw [card_insert_of_notMem ha] at hc ⊢
    rw [sum_insert ha]
    have hsq : 3 * (s.card + 1) ^ 2 = 3 * s.card ^ 2 + 6 * s.card + 3 := by ring
    simp only [id] at ih' ⊢
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' s.card
    · rw [hj] at ih' hc hsq ⊢
      have h1 : (2 * j) % 2 = 0 := by omega
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      rw [h1] at ih'
      rw [hsq, h2]
      omega
    · rw [hj] at ih' hc hsq ⊢
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
      rw [h1] at ih'
      rw [hsq, h2]
      omega

/-- Necessity: boundary size k forces 0 < k and 3k^2 <= 4n. -/
theorem le_of_exists (n k : ℕ) (hn : 0 < n) (S : Finset ℕ) (h0 : 0 ∉ S)
    (hs : S.sum id = n) (hb : bdry S = k) : 0 < k ∧ 3 * k ^ 2 ≤ 4 * n := by
  set B := S.filter (fun p => ¬ (p - 1 ∈ S ∧ p + 1 ∈ S)) with hBdef
  have hBk : B.card = k := hb
  have hpos : ∀ x ∈ B, 1 ≤ x := by
    intro x hx
    have hxS := (mem_filter.1 hx).1
    rcases Nat.eq_zero_or_pos x with rfl | h
    · exact absurd hxS h0
    · exact h
  have hN : NoThree B := by
    rintro x ⟨hx0, hx1, hx2⟩
    have h0' := (mem_filter.1 hx0).1
    have h2' := (mem_filter.1 hx2).1
    apply (mem_filter.1 hx1).2
    refine ⟨?_, ?_⟩
    · simpa using h0'
    · simpa [add_assoc] using h2'
  have hsum : B.sum id ≤ S.sum id := sum_le_sum_of_subset (filter_subset _ _)
  have hsb := sum_bound B hpos hN
  refine ⟨?_, ?_⟩
  · have hS0 : S.sum id ≠ 0 := by rw [hs]; omega
    have hne : S.Nonempty := nonempty_of_sum_ne_zero hS0
    rw [← hBk, card_pos]
    refine ⟨S.max' hne, mem_filter.2 ⟨max'_mem _ _, ?_⟩⟩
    rintro ⟨-, h⟩
    have := le_max' S _ h
    omega
  · have e1 : 3 * B.card ^ 2 ≤ 4 * B.sum id := le_trans (Nat.le_add_right _ _) hsb
    have e2 : 4 * B.sum id ≤ 4 * n := by rw [← hs]; exact Nat.mul_le_mul_left 4 hsum
    rw [← hBk]
    exact le_trans e1 e2

/-- Devlin's conjecture in A227345: for n >= 1, T(n,k) > 0 iff 0 < k and 3k^2 <= 4n. -/
theorem A227345_conjecture (n k : ℕ) (hn : 0 < n) :
    0 < T n k ↔ 0 < k ∧ 3 * k ^ 2 ≤ 4 * n := by
  rw [T_pos_iff]
  constructor
  · rintro ⟨S, h0, hs, hb⟩
    exact le_of_exists n k hn S h0 hs hb
  · rintro ⟨hk, h⟩
    exact exists_of_le n k hk h

/-- The same statement in the entry's wording, 0 < k^2 * 3/4 <= n over the reals. -/
theorem A227345_conjecture_real (n k : ℕ) (hn : 0 < n) :
    0 < T n k ↔ ((0 : ℝ) < (k : ℝ) ^ 2 * 3 / 4 ∧ (k : ℝ) ^ 2 * 3 / 4 ≤ n) := by
  rw [A227345_conjecture n k hn]
  constructor
  · rintro ⟨hk, h⟩
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h' : ((3 * k ^ 2 : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact ⟨by positivity, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h1
      · exact hk
    · have h' : ((3 * k ^ 2 : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h'

