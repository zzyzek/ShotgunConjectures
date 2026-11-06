import Mathlib

/-
OEIS A078537 (number of partitions of 4^n into powers of 4) and A078536
(Hanna's matrix: lower triangular, M(n,0) = 1, M(k,k) = 1, [M^4](i,j) = M(i+1,j+1)).
Conjecture (A078537, A078536): the sum of row n of A078536 is A078537(n).
Also the conjectured formula of A078536: M(n,k) = number of partitions of
4^n - 4^(n-k) into powers of 4 at most 4^(n-k).

Definitions.
* `t q m c`: Bakoev's count of partitions of c q^m into 1, q, ..., q^m,
  t q 0 c = 1, t q (m+1) c = sum_{i <= c} t q m (q i).
* `mm X Y i j = sum_{l <= i} X i l * Y l j` (product of lower-triangular matrices),
  `mm4 M = mm M (mm M (mm M M))`.
* `a n`: number of `p : Nat.Partition (4^n)` with every part a power of 4 (OEIS definition).
* `P q s n k = t q (n-k) (s q^k - 1)` for k <= n, else 0.

Main theorems.
* `A078537_conj`: every M : ℕ → ℕ → ℤ with M i j = 0 (i < j), M i 0 = 1 and
  mm4 M i j = M (i+1) (j+1) has sum_{k <= n} M n k = a n.
* `A078536_formula`: such an M has M n k = t 4 (n-k) (4^k - 1) for k <= n.
* `A078536_exists`: P 4 1 has all the defining properties (so the hypotheses are
  satisfiable and A078536 is P 4 1).
Route: `conv` (sum_j t(m-j, A q^j - 1) t(j, b) = t(m, A + b), induction on m and b),
`sum_one` (its b = 0 case), `left_mul` (P 1 * P s = P (s+1)), `M_eq` (uniqueness,
row by row), `ways_Lq` and `a_eq_t` (a n = t 4 n 1 via the coin-change count, the
`ways`/`msets` machinery copied from OEIS/A078128).

Not checked in this file: agreement with the OEIS data (certificate/check.py).
-/

namespace A078537

open Finset

/-- `t q m c`: partitions of c q^m into parts 1, q, ..., q^m (Bakoev's recursion). -/
def t (q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, c => ∑ i ∈ range (c + 1), t q m (q * i)

theorem t_zero_left (q c : ℕ) : t q 0 c = 1 := rfl

theorem t_zero_right (q : ℕ) : ∀ m, t q m 0 = 1
  | 0 => rfl
  | m + 1 => by simp [t, t_zero_right q m]

theorem t_succ_succ (q m c : ℕ) : t q (m + 1) (c + 1) = t q (m + 1) c + t q m (q * (c + 1)) := by
  simp only [t]; rw [Finset.sum_range_succ]

/-- Sum over the largest part: Σ_j t(m-j, A q^j - 1) = t(m, A). -/
theorem sum_one (q : ℕ) (hq : 1 ≤ q) : ∀ (m A : ℕ), 1 ≤ A →
    ∑ j ∈ range (m + 1), t q (m - j) (A * q ^ j - 1) = t q m A
  | 0, A, _ => by simp [t]
  | m + 1, A, hA => by
    rw [Finset.sum_range_succ']
    have hAq : 1 ≤ A * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h := sum_one q hq m (A * q) hAq
    have e : ∀ j ∈ range (m + 1), t q (m + 1 - (j + 1)) (A * q ^ (j + 1) - 1)
        = t q (m - j) (A * q * q ^ j - 1) := by
      intro j _; rw [show m + 1 - (j + 1) = m - j by omega, pow_succ]; ring_nf
    rw [Finset.sum_congr rfl e, h]
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    rw [t_succ_succ]
    simp only [Nat.sub_zero, pow_zero, mul_one, Nat.add_sub_cancel]
    ring_nf

/-- The convolution identity Σ_j t(m-j, A q^j - 1) t(j, b) = t(m, A + b). -/
theorem conv (q : ℕ) (hq : 1 ≤ q) : ∀ (m A b : ℕ), 1 ≤ A →
    ∑ j ∈ range (m + 1), t q (m - j) (A * q ^ j - 1) * t q j b = t q m (A + b)
  | m, A, 0, hA => by
    simp only [t_zero_right, mul_one, add_zero]; exact sum_one q hq m A hA
  | 0, A, b + 1, hA => by simp [t]
  | m + 1, A, b + 1, hA => by
    have hAq : 1 ≤ A * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have ih1 := conv q hq (m + 1) A b hA
    have ih2 := conv q hq m (A * q) (q * (b + 1)) hAq
    rw [Finset.sum_range_succ'] at ih1 ⊢
    have e : ∀ j ∈ range (m + 1),
        t q (m + 1 - (j + 1)) (A * q ^ (j + 1) - 1) * t q (j + 1) (b + 1) =
        t q (m + 1 - (j + 1)) (A * q ^ (j + 1) - 1) * t q (j + 1) b +
        t q (m - j) (A * q * q ^ j - 1) * t q j (q * (b + 1)) := by
      intro j _
      rw [t_succ_succ, show m + 1 - (j + 1) = m - j by omega, pow_succ]
      ring_nf
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih2]
    have h0 : t q 0 (b + 1) = t q 0 b := rfl
    rw [h0]
    rw [show A + (b + 1) = (A + b) + 1 by ring, t_succ_succ, ← ih1,
      show A * q + q * (b + 1) = q * (A + b + 1) by ring]
    ring


/-- Product of lower-triangular matrices (row i uses columns 0..i). -/
def mm (X Y : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ := ∑ l ∈ range (i + 1), X i l * Y l j

/-- The fourth power M^4 = M (M (M M)). -/
def mm4 (M : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ := mm M (mm M (mm M M))

/-- Candidate for the s-th power: P s n k = t(n-k, s q^k - 1) for k ≤ n. -/
def P (q s n k : ℕ) : ℤ := if k ≤ n then (t q (n - k) (s * q ^ k - 1) : ℤ) else 0

theorem left_mul (q : ℕ) (hq : 1 ≤ q) (s : ℕ) (hs : 1 ≤ s) (n k : ℕ) :
    mm (P q 1) (P q s) n k = P q (s + 1) n k := by
  unfold mm
  by_cases hkn : k ≤ n
  · rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ n + 1 by omega)]
    have hz : ∑ l ∈ range k, P q 1 n l * P q s l k = 0 :=
      Finset.sum_eq_zero (fun l hl => by
        have := Finset.mem_range.mp hl; simp [P, show ¬ k ≤ l by omega])
    rw [hz, zero_add, Finset.sum_Ico_eq_sum_range, show n + 1 - k = (n - k) + 1 by omega]
    have hA : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have hc := conv q hq (n - k) (q ^ k) (s * q ^ k - 1) hA
    have e : ∀ j ∈ range (n - k + 1), P q 1 n (k + j) * P q s (k + j) k =
        ((t q (n - k - j) (q ^ k * q ^ j - 1) * t q j (s * q ^ k - 1) : ℕ) : ℤ) := by
      intro j hj
      have := Finset.mem_range.mp hj
      simp only [P, show k + j ≤ n by omega, show k ≤ k + j by omega, ite_true, one_mul,
        show n - (k + j) = n - k - j by omega, show k + j - k = j by omega, pow_add]
      push_cast; ring
    rw [Finset.sum_congr rfl e, ← Nat.cast_sum, hc]
    simp only [P, hkn, ite_true]
    congr 2
    have : 1 ≤ s * q ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [add_mul, one_mul]; omega
  · have : ∀ l ∈ range (n + 1), P q 1 n l * P q s l k = 0 := by
      intro l hl
      have := Finset.mem_range.mp hl
      simp [P, show ¬ k ≤ l by omega]
    rw [Finset.sum_eq_zero this]
    simp [P, hkn]

theorem mm_congr (n : ℕ) (X X' Y Y' : ℕ → ℕ → ℤ)
    (hX : ∀ i ≤ n, ∀ k, X i k = X' i k) (hY : ∀ i ≤ n, ∀ k, Y i k = Y' i k) :
    ∀ i ≤ n, ∀ k, mm X Y i k = mm X' Y' i k := by
  intro i hi k
  unfold mm
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have := Finset.mem_range.mp hl
  rw [hX i hi l, hY l (by omega) k]

theorem P4 (n j : ℕ) : mm4 (P 4 1) n j = P 4 4 n j := by
  have h2 : mm (P 4 1) (P 4 1) = P 4 2 := by
    funext a b; exact left_mul 4 (by norm_num) 1 le_rfl a b
  have h3 : mm (P 4 1) (P 4 2) = P 4 3 := by
    funext a b; exact left_mul 4 (by norm_num) 2 (by norm_num) a b
  unfold mm4
  rw [h2, h3]
  exact left_mul 4 (by norm_num) 3 (by norm_num) n j

/-- Any matrix with Hanna's defining properties equals P 4 1. -/
theorem M_eq (M : ℕ → ℕ → ℤ) (hlow : ∀ i j, i < j → M i j = 0) (h0 : ∀ i, M i 0 = 1)
    (h4 : ∀ i j, mm4 M i j = M (i + 1) (j + 1)) : ∀ n k, M n k = P 4 1 n k := by
  have key : ∀ n, ∀ i ≤ n, ∀ k, M i k = P 4 1 i k := by
    intro n
    induction n with
    | zero =>
      intro i hi k
      obtain rfl : i = 0 := by omega
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [h0]; simp [P, t]
      · rw [hlow 0 k hk]; simp [P, show ¬ k ≤ 0 by omega]
    | succ n ih =>
      intro i hi k
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact ih i (by omega) k
      obtain rfl : i = n + 1 := by omega
      rcases k with _ | j
      · rw [h0]; simp [P, t_zero_right]
      · rw [← h4 n j]
        have hc1 := mm_congr n M (P 4 1) M (P 4 1) ih ih
        have hc2 := mm_congr n M (P 4 1) _ _ ih hc1
        have hc3 := mm_congr n M (P 4 1) _ _ ih hc2
        unfold mm4
        rw [hc3 n le_rfl j]
        have := P4 n j
        unfold mm4 at this
        rw [this]
        unfold P
        by_cases hj : j ≤ n
        · simp only [hj, show j + 1 ≤ n + 1 by omega, ite_true, show n + 1 - (j + 1) = n - j by omega,
            pow_succ]
          ring_nf
        · simp [hj, show ¬ j + 1 ≤ n + 1 by omega]
  exact fun n k => key n n le_rfl k
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

/-- The coins q^m, ..., q, 1. -/
def Lq (q : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | m + 1 => q ^ (m + 1) :: Lq q m

theorem mem_Lq (q : ℕ) : ∀ m x, x ∈ Lq q m ↔ ∃ j ≤ m, x = q ^ j
  | 0, x => by simp [Lq]
  | m + 1, x => by
    simp only [Lq, List.mem_cons, mem_Lq q m x]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨m + 1, le_rfl, h⟩
      · exact ⟨j, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_or_ge j (m + 1) with hl | hl
      · exact Or.inr ⟨j, by omega, h⟩
      · left; rw [h, show j = m + 1 by omega]

theorem Lq_pos (q : ℕ) (hq : 1 ≤ q) (m : ℕ) : ∀ c ∈ Lq q m, 0 < c := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := (mem_Lq q m c).mp hc
  positivity

theorem Lq_nodup (q : ℕ) (hq : 2 ≤ q) : ∀ m, (Lq q m).Nodup
  | 0 => by simp [Lq]
  | m + 1 => by
    rw [Lq, List.nodup_cons]
    refine ⟨fun h => ?_, Lq_nodup q hq m⟩
    obtain ⟨j, hj, he⟩ := (mem_Lq q m _).mp h
    have := Nat.pow_lt_pow_right (show 1 < q by omega) (show j < m + 1 by omega)
    omega

theorem ways_Lq (q : ℕ) (hq : 1 ≤ q) : ∀ m c, ways (Lq q m) (c * q ^ m) = t q m c
  | 0, c => by
    simp only [Lq, ways, pow_zero, mul_one, Nat.div_one, list_sum_range]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
      have := Finset.mem_range.mp hj; simp [show c - j ≠ 0 by omega])]
    simp [t]
  | m + 1, c => by
    have hp : 0 < q ^ (m + 1) := by positivity
    rw [Lq, ways, list_sum_range, Nat.mul_div_cancel _ hp, t]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := Finset.mem_range.mp hj
    rw [← ways_Lq q hq m (q * j)]
    congr 1
    rw [← Nat.sub_mul, show c - (c + 1 - 1 - j) = j by omega, pow_succ]
    ring

open Classical in
/-- A078537(n): the number of partitions of 4^n into powers of 4. -/
noncomputable def a (n : ℕ) : ℕ :=
  (univ.filter (fun p : (4 ^ n).Partition => ∀ i ∈ p.parts, ∃ j, i = 4 ^ j)).card

theorem a_eq_t (n : ℕ) : a n = t 4 n 1 := by
  classical
  rw [← ways_Lq 4 (by norm_num) n 1, one_mul,
    ← card_msets (Lq 4 n) (4 ^ n) (Lq_pos 4 (by norm_num) n) (Lq_nodup 4 (by norm_num) n)]
  unfold a
  apply Finset.card_bij (fun p _ => p.parts)
  · intro p hp
    rw [mem_filter] at hp
    rw [mem_msets _ _ _ (Lq_pos 4 (by norm_num) n)]
    refine ⟨p.parts_sum, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ := hp.2 i hi
    have hle := Nat.Partition.le_of_mem_parts hi
    refine (mem_Lq 4 n _).mpr ⟨j, ?_, rfl⟩
    by_contra hj
    have := Nat.pow_lt_pow_right (show 1 < 4 by norm_num) (show n < j by omega)
    omega
  · intro p _ p' _ h; exact Nat.Partition.ext h
  · intro s hs
    rw [mem_msets _ _ _ (Lq_pos 4 (by norm_num) n)] at hs
    refine ⟨⟨s, fun hi => Lq_pos 4 (by norm_num) n _ (hs.2 _ hi), hs.1⟩, ?_, rfl⟩
    rw [mem_filter]
    refine ⟨mem_univ _, fun i hi => ?_⟩
    obtain ⟨j, -, h⟩ := (mem_Lq 4 n i).mp (hs.2 i hi)
    exact ⟨j, h⟩

/-- A078536 is determined by its definition: M(n, k) = t(n-k, 4^k - 1), i.e. the number of
partitions of 4^n - 4^(n-k) into powers of 4 at most 4^(n-k) (the entry's conjectured formula). -/
theorem A078536_formula (M : ℕ → ℕ → ℤ) (hlow : ∀ i j, i < j → M i j = 0)
    (h0 : ∀ i, M i 0 = 1) (h4 : ∀ i j, mm4 M i j = M (i + 1) (j + 1)) (n k : ℕ) (hk : k ≤ n) :
    M n k = (t 4 (n - k) (4 ^ k - 1) : ℤ) := by
  rw [M_eq M hlow h0 h4]; simp [P, hk]

/-- The conjecture of A078537: the sum of row n of A078536 is A078537(n). -/
theorem A078537_conj (M : ℕ → ℕ → ℤ) (hlow : ∀ i j, i < j → M i j = 0)
    (h0 : ∀ i, M i 0 = 1) (h4 : ∀ i j, mm4 M i j = M (i + 1) (j + 1)) (n : ℕ) :
    ∑ k ∈ range (n + 1), M n k = a n := by
  rw [a_eq_t, ← sum_one 4 (by norm_num) n 1 le_rfl]
  push_cast
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [A078536_formula M hlow h0 h4 n k (by have := Finset.mem_range.mp hk; omega), one_mul]

/-- Hanna's matrix exists: P 4 1 satisfies the definition (with M(k,k) = 1). -/
theorem A078536_exists :
    (∀ i j, i < j → P 4 1 i j = 0) ∧ (∀ i, P 4 1 i 0 = 1) ∧ (∀ i, P 4 1 i i = 1) ∧
    (∀ i j, mm4 (P 4 1) i j = P 4 1 (i + 1) (j + 1)) := by
  refine ⟨fun i j h => by simp [P, show ¬ j ≤ i by omega], fun i => by simp [P, t_zero_right],
    fun i => by simp [P, t], fun i j => ?_⟩
  rw [P4]
  unfold P
  by_cases hj : j ≤ i
  · simp only [hj, show j + 1 ≤ i + 1 by omega, ite_true, show i + 1 - (j + 1) = i - j by omega,
      pow_succ]
    ring_nf
  · simp [hj, show ¬ j + 1 ≤ i + 1 by omega]
