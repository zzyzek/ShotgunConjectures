import Mathlib

/-
OEIS A078130: numbers having exactly one representation as a sum of cubes > 1
(A078128(n) = 1).  Conjecture (entry): the sequence is finite; is
a(63) = 218 the last entry?  Answer: yes.

Definitions.
* `IsCube2 i`: i = k^3 for some k ≥ 2.
* `a n`: A078128(n), the number of `p : Nat.Partition n` all of whose parts
  satisfy `IsCube2` (the OEIS definition).
* `IsA078130 n`: 1 ≤ n ∧ a n = 1 (offset 1, so n ≥ 1).
* `S`: the 63 data terms of A078130.

Main theorems.
* `A078130_iff`: IsA078130 n ↔ n ∈ S.
* `A078130_finite`, `A078130_le`: the set is finite and every term is ≤ 218.
* `A078130_nth`: Nat.nth IsA078130 62 = 218 (a(63) = 218 with offset 1) and
  `A078130_ncard`: the set has exactly 63 elements.
Route: `a_eq_ways`: for n < 512 the parts are among 8, 27, 64, 125, 216, 343,
so a n = ways L6 n (coin-change count, `card_msets`, `mem_msets`), evaluated
by the kernel for n < 398; `a_lower` (only 8 and 27) gives a n ≥ 2 for
n ≥ 398.

Not checked in this file: none of the claim; certificate/check.py repeats the
computation in Python.
-/

namespace A078130

open Finset

/-- `i` is a cube `k ^ 3` with `k ≥ 2`. -/
def IsCube2 (i : ℕ) : Prop := ∃ k, 2 ≤ k ∧ k ^ 3 = i

open Classical in
/-- A078128(n): the number of partitions of `n` into cubes > 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  (univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, IsCube2 i)).card

/-- Number of multisets with elements in `L` and sum `n` (coin-change count). -/
def ways : List ℕ → ℕ → ℕ
  | [], n => if n = 0 then 1 else 0
  | c :: cs, n => ((List.range (n / c + 1)).map (fun j => ways cs (n - j * c))).sum

/-- The multisets counted by `ways`. -/
def msets : List ℕ → ℕ → Finset (Multiset ℕ)
  | [], n => if n = 0 then {0} else ∅
  | c :: cs, n => (range (n / c + 1)).biUnion
      (fun j => (msets cs (n - j * c)).image (fun s => Multiset.replicate j c + s))

theorem mem_msets : ∀ (L : List ℕ) (n : ℕ) (s : Multiset ℕ), (∀ c ∈ L, 0 < c) →
    (s ∈ msets L n ↔ s.sum = n ∧ ∀ x ∈ s, x ∈ L)
  | [], n, s, _ => by
    have h0 : (∀ x ∈ s, x ∈ ([] : List ℕ)) ↔ s = 0 := by
      simp [Multiset.eq_zero_iff_forall_notMem]
    rw [h0]
    by_cases hn : n = 0
    · subst hn
      show s ∈ ({0} : Finset (Multiset ℕ)) ↔ _
      rw [mem_singleton]
      exact ⟨fun h => ⟨by simp [h], h⟩, fun h => h.2⟩
    · show s ∈ (if n = 0 then {0} else ∅) ↔ _
      simp only [hn, ↓reduceIte]
      simp only [Finset.notMem_empty, false_iff, not_and]
      intro hs h
      subst h
      simp at hs
      exact hn hs.symm
  | c :: cs, n, s, hpos => by
    have hc : 0 < c := hpos c (by simp)
    have ih := fun m t => mem_msets cs m t (fun x hx => hpos x (by simp [hx]))
    simp only [msets, mem_biUnion, mem_range, mem_image]
    constructor
    · rintro ⟨j, hj, t, ht, rfl⟩
      rw [ih] at ht
      obtain ⟨hts, htL⟩ := ht
      have hjc : j * c ≤ n :=
        calc j * c ≤ n / c * c := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp hj)
          _ ≤ n := Nat.div_mul_le_self n c
      refine ⟨?_, ?_⟩
      · rw [Multiset.sum_add, Multiset.sum_replicate, hts, smul_eq_mul]; omega
      · intro x hx
        rcases Multiset.mem_add.mp hx with h | h
        · rw [Multiset.eq_of_mem_replicate h]; simp
        · simp [htL x h]
    · rintro ⟨hs, hL⟩
      have hsplit : Multiset.replicate (s.count c) c + s.filter (fun x => ¬ x = c) = s := by
        rw [← Multiset.filter_eq' s c]; exact Multiset.filter_add_not _ s
      have hsum := hs
      rw [← hsplit, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hsum
      refine ⟨s.count c, ?_, s.filter (fun x => ¬ x = c), ?_, hsplit⟩
      · exact Nat.lt_succ_iff.mpr ((Nat.le_div_iff_mul_le hc).mpr (by omega))
      · rw [ih]
        refine ⟨by omega, ?_⟩
        intro x hx
        rw [Multiset.mem_filter] at hx
        have := hL x hx.1
        simp only [List.mem_cons] at this
        rcases this with h | h
        · exact absurd h hx.2
        · exact h

theorem list_sum_range (f : ℕ → ℕ) : ∀ k, ((List.range k).map f).sum = ∑ j ∈ range k, f j
  | 0 => by simp
  | k + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f k,
      Finset.sum_range_succ]; simp

theorem card_msets : ∀ (L : List ℕ) (n : ℕ), (∀ c ∈ L, 0 < c) → L.Nodup →
    (msets L n).card = ways L n
  | [], n, _, _ => by by_cases hn : n = 0 <;> simp [msets, ways, hn]
  | c :: cs, n, hpos, hnd => by
    have hpos' : ∀ x ∈ cs, 0 < x := fun x hx => hpos x (by simp [hx])
    have hcn : c ∉ cs := (List.nodup_cons.mp hnd).1
    rw [msets, card_biUnion]
    · rw [ways, list_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [card_image_of_injective _ (add_right_injective _),
        card_msets cs _ hpos' (List.nodup_cons.mp hnd).2]
    · intro j _ j' _ hjj'
      rw [Function.onFun, disjoint_left]
      intro u hu hu'
      simp only [mem_image] at hu hu'
      obtain ⟨t, ht, rfl⟩ := hu
      obtain ⟨t', ht', he⟩ := hu'
      have h1 : Multiset.count c t = 0 := Multiset.count_eq_zero.mpr
        (fun h => hcn (((mem_msets cs _ t hpos').1 ht).2 c h))
      have h2 : Multiset.count c t' = 0 := Multiset.count_eq_zero.mpr
        (fun h => hcn (((mem_msets cs _ t' hpos').1 ht').2 c h))
      have := congrArg (Multiset.count c) he
      simp only [Multiset.count_add, Multiset.count_replicate_self, h1, h2, add_zero] at this
      exact hjj' this.symm

/-- The cubes > 1 below 512. -/
def L6 : List ℕ := [343, 216, 125, 64, 27, 8]

theorem mem_L6_of_cube (i : ℕ) (h : IsCube2 i) (hi : i < 512) : i ∈ L6 := by
  obtain ⟨k, hk, rfl⟩ := h
  have : k < 8 := by
    by_contra hk8
    have := Nat.pow_le_pow_left (Nat.le_of_not_lt hk8) 3
    omega
  interval_cases k <;> simp [L6]

theorem cube_of_mem_L6 (i : ℕ) (h : i ∈ L6) : IsCube2 i := by
  simp only [L6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨7, by norm_num, rfl⟩, ⟨6, by norm_num, rfl⟩, ⟨5, by norm_num, rfl⟩,
    ⟨4, by norm_num, rfl⟩, ⟨3, by norm_num, rfl⟩, ⟨2, le_rfl, rfl⟩]

theorem L6_pos : ∀ c ∈ L6, 0 < c := by decide

/-- For `n < 512`, A078128(n) is the coin-change count with coins 8, 27, ..., 343. -/
theorem a_eq_ways (n : ℕ) (hn : n < 512) : a n = ways L6 n := by
  classical
  rw [← card_msets L6 n L6_pos (by decide)]
  unfold a
  apply Finset.card_bij (fun p _ => p.parts)
  · intro p hp
    rw [mem_filter] at hp
    rw [mem_msets L6 n _ L6_pos]
    exact ⟨p.parts_sum, fun i hi => mem_L6_of_cube i (hp.2 i hi)
      (lt_of_le_of_lt (Nat.Partition.le_of_mem_parts hi) hn)⟩
  · intro p _ q _ h; exact Nat.Partition.ext h
  · intro s hs
    rw [mem_msets L6 n _ L6_pos] at hs
    refine ⟨⟨s, fun hi => L6_pos _ (hs.2 _ hi), hs.1⟩, ?_, rfl⟩
    rw [mem_filter]
    exact ⟨mem_univ _, fun i hi => cube_of_mem_L6 i (hs.2 i hi)⟩

/-- Every `r ≥ 182` is `8 x + 27 y`. -/
theorem rep (r : ℕ) (hr : 182 ≤ r) :
    8 * ((r - 27 * (3 * r % 8)) / 8) + 27 * (3 * r % 8) = r := by omega

/-- Lower bound: if `n ≥ 216 m + 182` then A078128(n) ≥ m + 1. -/
theorem a_lower (m n : ℕ) (hn : 216 * m + 182 ≤ n) : m + 1 ≤ a n := by
  classical
  set r := n - 216 * m with hr
  set y := 3 * r % 8
  set x := (r - 27 * y) / 8
  have hxy : 8 * x + 27 * y = r := rep r (by omega)
  let f : ℕ → Multiset ℕ := fun j =>
    Multiset.replicate (y + 8 * (m - j)) 27 + Multiset.replicate (x + 27 * j) 8
  have hf : Set.InjOn f (range (m + 1) : Set ℕ) := by
    intro j _ j' _ h
    have := congrArg (Multiset.count 8) h
    simp [f, Multiset.count_add, Multiset.count_replicate] at this
    omega
  have hsub : (range (m + 1)).image f ⊆
      (univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, IsCube2 i)).image
        (fun p => p.parts) := by
    intro s hs
    simp only [mem_image, mem_range] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    simp only [mem_image, mem_filter, mem_univ, true_and]
    have hsum : (f j).sum = n := by
      simp only [f, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have : j ≤ m := Nat.lt_succ_iff.mp hj
      have h2 : (y + 8 * (m - j)) * 27 + (x + 27 * j) * 8 = 8 * x + 27 * y + 216 * m := by
        have : m - j + j = m := Nat.sub_add_cancel this
        nlinarith
      omega
    have hmem : ∀ i ∈ f j, i = 27 ∨ i = 8 := by
      intro i hi
      rcases Multiset.mem_add.mp hi with h | h
      · exact Or.inl (Multiset.eq_of_mem_replicate h)
      · exact Or.inr (Multiset.eq_of_mem_replicate h)
    refine ⟨⟨f j, fun hi => by rcases hmem _ hi with rfl | rfl <;> norm_num, hsum⟩, ?_, rfl⟩
    intro i hi
    rcases hmem i hi with rfl | rfl
    exacts [⟨3, by norm_num, rfl⟩, ⟨2, le_rfl, rfl⟩]
  have h1 := card_le_card hsub
  rw [card_image_of_injOn hf, card_range] at h1
  exact h1.trans card_image_le


/-- Kernel check: A078128(n) ≥ 2 for 218 < n < 398 (coin-change count). -/
theorem chk1 : ∀ n < 398, 218 < n → 2 ≤ ways L6 n := by decide +kernel

/-- b(1) = 218 is sharp: A078128(218) = 1 and A078128(n) ≥ 2 for n > 218. -/
theorem A078128_b1 : a 218 = 1 ∧ ∀ n, 218 < n → 1 < a n := by
  refine ⟨by rw [a_eq_ways 218 (by norm_num)]; decide +kernel, fun n hn => ?_⟩
  by_cases h : n < 398
  · rw [a_eq_ways n (by omega)]; exact chk1 n h hn
  · exact a_lower 1 n (by omega)

/-- The 63 terms of A078130 (OEIS data). -/
def S : List ℕ := [8, 16, 24, 27, 32, 35, 40, 43, 48, 51, 54, 56, 59, 62, 67, 70, 75, 78, 81, 83, 86, 89, 94, 97, 102, 105, 108, 110, 113, 116, 121, 124, 125, 129, 132, 133, 135, 137, 140, 141, 143, 148, 149, 151, 156, 157, 159, 162, 164, 165, 167, 170, 173, 175, 178, 181, 183, 186, 191, 194, 202, 210, 218]

/-- A078130 as a predicate (offset 1). -/
def IsA078130 (n : ℕ) : Prop := 1 ≤ n ∧ a n = 1

/-- Kernel check below 219. -/
theorem chkS : ∀ n < 219, (1 ≤ n ∧ ways L6 n = 1 ↔ n ∈ S) := by decide +kernel

theorem A078130_iff (n : ℕ) : IsA078130 n ↔ n ∈ S := by
  unfold IsA078130
  by_cases h : n < 219
  · rw [a_eq_ways n (by omega)]; exact chkS n h
  · have h1 : 1 < a n := A078128_b1.2 n (by omega)
    have h2 : ∀ x ∈ S, x ≤ 218 := by decide
    constructor
    · rintro ⟨-, h3⟩; omega
    · intro hS; have := h2 n hS; omega

theorem A078130_le (n : ℕ) (h : IsA078130 n) : n ≤ 218 := by
  have h2 : ∀ x ∈ S, x ≤ 218 := by decide
  exact h2 n ((A078130_iff n).1 h)

theorem A078130_finite : {n | IsA078130 n}.Finite :=
  (Set.finite_Iic 218).subset fun n hn => A078130_le n hn

theorem A078130_eq : {n | IsA078130 n} = {n | n ∈ S} := Set.ext fun n => A078130_iff n

theorem A078130_ncard : {n | IsA078130 n}.ncard = 63 := by
  rw [A078130_eq, show {n | n ∈ S} = ((S.toFinset : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset]
  decide +kernel

theorem A078130_nth : Nat.nth IsA078130 62 = 218 := by
  have hp : IsA078130 = fun n => n ∈ S := funext fun n => propext (A078130_iff n)
  rw [hp]
  have h := Nat.nth_count (p := fun n => n ∈ S) (n := 218) (by decide)
  have hc : Nat.count (fun n => n ∈ S) 218 = 62 := by decide +kernel
  rw [hc] at h
  exact h
