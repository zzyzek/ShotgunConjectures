import Mathlib

/-
OEIS A113676 (Floor van Lamoen, Paul D. Hanna): rows of Golomb's sequence A001462 with one
fewer 2 (1, 2, 3, 3, 4, 4, 4, ...): row 1 is [1], row n takes the next (row sum of row n-1)
elements; a(n) = number of elements of row n.
Conjectures: (1) a(n) for n > 1 gives the first differences of A014644(n) for n >= 3, i.e.
a(n) = A014644(n+2) - A014644(n+1) for n >= 2; (2) the final elements of the rows form A014644
except for the duplicate 2.  A014644: array starting with {1,1}, the i-th term of a row gives the
number of i's in the next row; final term of each row.

Definitions.  `gam` is that row operator (i-th entry c gives c copies of i); `R k = gam^k [2]`,
so R 1 = [1,1] and `A014644 n` is the final term of `R n`.  `golomb n` is read off `R (n+2)`;
`golomb_unique` proves that every g with g(1) = 1, nondecreasing, and each n >= 1 occurring
exactly g(n) times (the definition of A001462) agrees with `golomb` on n >= 1.  `H` is Golomb's
sequence with one 2 removed, `st`/`row` build the triangle, `A113676 n` is the length of row n.

Main theorems.
* `A113676_differences`: n >= 2 → A113676 n = A014644 (n+2) - A014644 (n+1).
* `A113676_final_one`, `A113676_final`: row 1 ends in A014644 1, row n (n >= 2) ends in
  A014644 (n+1).
* `golomb_unique` (identifies `golomb` with A001462).

Route.  `R_prefix`: R k (k >= 2) are nested prefixes; `Gl_R`: they are prefixes of `golomb`.
`key`: R (k+3) = R (k+2) ++ row (k+2), by induction with the invariant `Inv`: rows 1..k+1 hold
|R (k+2)| - 1 elements.  `A014644_succ`: A014644 (m+1) = |R m|.
Checked: all of the above.  Not checked: agreement with the OEIS data terms
(certificate/check.py).
-/

namespace OEIS_A113676

/-- The golombic operator: the i-th entry c (1-indexed) of `l` contributes c copies of i. -/
def gam (l : List ℕ) : List ℕ := (l.mapIdx fun i c => List.replicate c (i + 1)).flatten

/-- Rows of the array of A014643/A014644: row 1 = [1, 1] = gam [2], row (k+1) = gam (row k). -/
def R (k : ℕ) : List ℕ := gam^[k] [2]

/-- A014644: final term of row n (n ≥ 1). -/
def A014644 (n : ℕ) : ℕ := (R n).getLast?.getD 0

/-- Golomb's sequence A001462 (1-indexed), read off the rows R k (k ≥ 2), which are its prefixes. -/
def golomb (n : ℕ) : ℕ := (R (n + 2)).getD (n - 1) 0

/-- Golomb's sequence with one 2 removed: 1, 2, 3, 3, 4, 4, 4, ... (1-indexed). -/
def H (j : ℕ) : ℕ := if j = 1 then 1 else golomb (j + 1)

/-- `st k = (S, row)`: row number k+1 of the triangle and the number S of elements in rows 1..k+1.
Row 1 is [1]; row n+1 consists of the next (row sum of row n) elements of `H`. -/
def st : ℕ → ℕ × List ℕ
  | 0 => (1, [1])
  | k + 1 =>
    let r := (List.range' ((st k).1 + 1) (st k).2.sum).map H
    ((st k).1 + r.length, r)

/-- Row n of the triangle (n ≥ 1). -/
def row (n : ℕ) : List ℕ := (st (n - 1)).2

/-- A113676: number of elements of row n. -/
def A113676 (n : ℕ) : ℕ := (row n).length

theorem length_gam (l : List ℕ) : (gam l).length = l.sum := by
  unfold gam
  rw [List.length_flatten]
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l c ih =>
    rw [List.mapIdx_append, List.map_append, List.sum_append, ih]
    simp

theorem gam_append (l t : List ℕ) :
    gam (l ++ t) = gam l ++ (t.mapIdx fun i c => List.replicate c (i + l.length + 1)).flatten := by
  unfold gam
  rw [List.mapIdx_append, List.flatten_append]

theorem gam_prefix {l l' : List ℕ} (h : l <+: l') : gam l <+: gam l' := by
  obtain ⟨t, rfl⟩ := h
  rw [gam_append]
  exact List.prefix_append _ _

theorem one_le_of_mem_gam (l : List ℕ) : ∀ x ∈ gam l, 1 ≤ x := by
  intro x hx
  simp only [gam, List.mem_flatten, List.mem_mapIdx] at hx
  obtain ⟨_, ⟨i, _, rfl⟩, hx⟩ := hx
  rw [List.mem_replicate] at hx
  omega

theorem getLast_gam (l : List ℕ) (c : ℕ) (hc : 1 ≤ c) :
    (gam (l ++ [c])).getLast?.getD 0 = (l ++ [c]).length := by
  rw [gam_append]
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  simp [List.replicate_succ', List.getLast?_append]

theorem R_succ (k : ℕ) : R (k + 1) = gam (R k) := by
  unfold R
  rw [Function.iterate_succ_apply']

theorem R_two : R 2 = [1, 2] := by decide
theorem R_three : R 3 = [1, 2, 2] := by decide

theorem one_le_of_mem_R (k : ℕ) : ∀ x ∈ R (k + 1), 1 ≤ x := by
  rw [R_succ]; exact one_le_of_mem_gam _

theorem R_prefix_succ (k : ℕ) : R (k + 2) <+: R (k + 3) := by
  induction k with
  | zero => rw [R_two, R_three]; exact ⟨[2], rfl⟩
  | succ k ih =>
    rw [R_succ (k + 2), R_succ (k + 1 + 2)]
    exact gam_prefix ih

theorem R_prefix (k m : ℕ) (h : k ≤ m) : R (k + 2) <+: R (m + 2) := by
  induction m with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact List.prefix_refl _
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · exact (ih (by omega)).trans (R_prefix_succ m)
    · obtain rfl : k = m + 1 := by omega
      exact List.prefix_refl _

theorem length_R_lt (k : ℕ) : (R (k + 2)).length < (R (k + 3)).length := by
  have hp : [1, 2] <+: R (k + 2) := by
    have := R_prefix 0 k (by omega); rwa [R_two] at this
  obtain ⟨t, ht⟩ := hp
  have hpos : ∀ x ∈ t, 1 ≤ x := by
    intro x hx
    exact one_le_of_mem_R (k + 1) x (by rw [← ht]; simp [hx])
  have ht1 := List.length_le_sum_of_one_le t hpos
  rw [show k + 3 = (k + 2) + 1 by omega, R_succ (k + 2), length_gam, ← ht]
  simp
  omega

theorem length_R (k : ℕ) : k + 2 ≤ (R (k + 2)).length := by
  induction k with
  | zero => rw [R_two]; simp
  | succ k ih => have := length_R_lt k; rw [show k + 1 + 2 = k + 3 by omega]; omega

theorem getD_R (k i : ℕ) (hi : i < (R (k + 2)).length) :
    (R (k + 2)).getD i 0 = golomb (i + 1) := by
  unfold golomb
  have hi' : i < (R (i + 1 + 2)).length := by have := length_R (i + 1); omega
  rw [show i + 1 - 1 = i by omega, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
  rcases Nat.le_total k (i + 1) with h | h
  · exact ((R_prefix k (i + 1) h).getElem hi).symm ▸ rfl
  · exact ((R_prefix (i + 1) k h).getElem hi') ▸ rfl

/-- Prefix of Golomb's sequence of length L. -/
def Gl (L : ℕ) : List ℕ := (List.range' 1 L).map golomb

theorem Gl_R (k : ℕ) : Gl (R (k + 2)).length = R (k + 2) := by
  apply List.ext_getElem
  · simp [Gl]
  · intro i h1 h2
    simp only [Gl, List.getElem_map, List.getElem_range']
    rw [← List.getD_eq_getElem _ 0 h2, getD_R k i h2]
    congr 1; omega

theorem Gl_add (a b : ℕ) : Gl (a + b) = Gl a ++ (List.range' (1 + a) b).map golomb := by
  unfold Gl
  rw [← List.map_append, show 1 + a = 1 + 1 * a by ring, List.range'_append]

theorem st_fst_pos (k : ℕ) : 1 ≤ (st k).1 := by
  induction k with
  | zero => simp [st]
  | succ k ih => simp only [st]; omega

theorem row_map (s n : ℕ) (hs : 1 ≤ s) :
    (List.range' (s + 1) n).map H = (List.range' (1 + (s + 1)) n).map golomb := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_map, List.getElem_range']
    unfold H
    split_ifs with h
    · omega
    · congr 1; omega

theorem st_succ_fst (k : ℕ) : (st (k + 1)).1 = (st k).1 + (st (k + 1)).2.length := rfl
theorem st_succ_snd (k : ℕ) :
    (st (k + 1)).2 = (List.range' ((st k).1 + 1) (st k).2.sum).map H := rfl
theorem length_st_succ (k : ℕ) : (st (k + 1)).2.length = (st k).2.sum := by
  rw [st_succ_snd]; simp

/-- Invariant: rows 1..k+1 hold (st k).1 elements, one fewer than row k+2 of the Levine array. -/
def Inv (k : ℕ) : Prop := (st k).1 + 1 = (R (k + 2)).length

theorem key (k : ℕ) (h0 : Inv k) (h1 : Inv (k + 1)) : R (k + 3) = R (k + 2) ++ (st (k + 1)).2 := by
  have e1 : R (k + 3) = Gl ((st k).1 + 1 + (st (k + 1)).2.length) := by
    rw [← Gl_R (k + 1)]; congr 1; unfold Inv at h1; rw [← h1, st_succ_fst]; omega
  have e2 : Gl ((st k).1 + 1) = R (k + 2) := by rw [h0, Gl_R]
  rw [e1, Gl_add, ← row_map _ _ (st_fst_pos k), e2, length_st_succ, ← st_succ_snd]

theorem inv_step (k : ℕ) (h0 : Inv k) (h1 : Inv (k + 1)) : Inv (k + 2) := by
  have hk := key k h0 h1
  unfold Inv at h1 ⊢
  have e2 : (R (k + 2 + 2)).length = (R (k + 3)).sum := by
    rw [show k + 2 + 2 = (k + 3) + 1 by omega, R_succ, length_gam]
  have e3 : (R (k + 3)).length = (R (k + 2)).sum := by
    rw [show k + 3 = (k + 2) + 1 by omega, R_succ, length_gam]
  rw [e2, st_succ_fst, length_st_succ]
  rw [hk, List.sum_append] at e2 ⊢
  rw [show k + 1 + 2 = k + 3 by omega] at h1
  omega

theorem inv_all (k : ℕ) : Inv k ∧ Inv (k + 1) := by
  induction k with
  | zero => exact ⟨by unfold Inv; rw [R_two]; rfl, by unfold Inv; rw [R_three]; rfl⟩
  | succ k ih => exact ⟨ih.2, inv_step k ih.1 ih.2⟩

theorem R_concat (m : ℕ) : ∃ l c, R m = l ++ [c] ∧ 1 ≤ c := by
  have hne : R m ≠ [] := by
    rcases m with _ | _ | j
    · decide
    · decide
    · intro h; have := length_R j; rw [h] at this; simp at this
  obtain h | ⟨l, c, hc⟩ := List.eq_nil_or_concat (R m)
  · exact absurd h hne
  · rw [List.concat_eq_append] at hc
    refine ⟨l, c, hc, ?_⟩
    rcases m with _ | j
    · rw [show R 0 = [2] from rfl] at hc
      have : c = 2 := by
        have := congrArg List.getLast? hc; simpa using this.symm
      omega
    · exact one_le_of_mem_R j c (by rw [hc]; simp)

theorem A014644_succ (m : ℕ) : A014644 (m + 1) = (R m).length := by
  obtain ⟨l, c, hc, h1⟩ := R_concat m
  unfold A014644
  rw [R_succ, hc, getLast_gam l c h1]

/-- First conjecture of A113676: for n ≥ 2, a(n) = A014644(n+2) - A014644(n+1),
i.e. a(n) for n > 1 gives the first differences of A014644 from its third term. -/
theorem A113676_differences (n : ℕ) (hn : 2 ≤ n) :
    A113676 n = A014644 (n + 2) - A014644 (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk := key k (inv_all k).1 (inv_all k).2
  rw [A014644_succ, A014644_succ, show k + 2 + 1 = k + 3 by omega, hk]
  unfold A113676 row
  simp

/-- Second conjecture of A113676: the final elements of the rows are A014644 with its
duplicate 2 removed: row 1 ends in A014644(1) = 1 and row n (n ≥ 2) ends in A014644(n+1). -/
theorem A113676_final_one : (row 1).getLast?.getD 0 = A014644 1 := by
  rw [A014644_succ]; rfl

theorem A113676_final (n : ℕ) (hn : 2 ≤ n) : (row n).getLast?.getD 0 = A014644 (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk := key k (inv_all k).1 (inv_all k).2
  have hlt := length_R_lt k
  have hne : (st (k + 1)).2 ≠ [] := by
    intro h; rw [hk, h] at hlt; simp at hlt
  unfold A014644 row
  rw [show k + 2 + 1 = k + 3 by omega, hk, List.getLast?_append]
  rw [show k + 2 - 1 = k + 1 by omega]
  obtain ⟨l, c, hc⟩ := (List.eq_nil_or_concat _).resolve_left hne
  rw [List.concat_eq_append] at hc
  rw [hc]; simp


/-! ### `golomb` is Golomb's sequence

A001462: a(n) is the number of times n occurs, starting with a(1) = 1 (nondecreasing).
Every g : ℕ → ℕ with these properties agrees with `golomb` on n ≥ 1 (`golomb_unique`). -/

theorem ncard_Ioc' (a b : ℕ) : (Set.Ioc a b).ncard = b - a := by
  rw [← Finset.coe_Ioc, Set.ncard_coe_finset, Nat.card_Ioc]

theorem ncard_Ioo' (a b : ℕ) : (Set.Ioo a b).ncard = b - a - 1 := by
  rw [← Finset.coe_Ioo, Set.ncard_coe_finset, Nat.card_Ioo]

/-- A finite set of size c ≥ 1 above a, closed downwards above a, is (a, a + c]. -/
theorem interval_of_down (F : Set ℕ) (a c : ℕ) (hF : F.ncard = c) (hc : 1 ≤ c)
    (hlow : ∀ j ∈ F, a < j) (hdown : ∀ j ∈ F, ∀ j', a < j' → j' ≤ j → j' ∈ F) :
    ∀ j, j ∈ F ↔ a < j ∧ j ≤ a + c := by
  have hfin : F.Finite := Set.finite_of_ncard_pos (by omega)
  intro j
  constructor
  · intro hj
    refine ⟨hlow j hj, ?_⟩
    by_contra hgt
    have hsub : Set.Ioc a j ⊆ F := fun j' hj' => hdown j hj j' hj'.1 hj'.2
    have := Set.ncard_le_ncard hsub hfin
    rw [ncard_Ioc'] at this
    omega
  · rintro ⟨h1, h2⟩
    by_contra hj
    have hsub : F ⊆ Set.Ioo a j := by
      intro x hx
      refine ⟨hlow x hx, ?_⟩
      by_contra hxj
      exact hj (hdown x hx j h1 (by omega))
    have := Set.ncard_le_ncard hsub
    rw [ncard_Ioo'] at this
    omega

section unique

variable (g : ℕ → ℕ)

/-- Prefix of g of length L. -/
def gl (L : ℕ) : List ℕ := (List.range' 1 L).map g

theorem gl_add (a b : ℕ) : gl g (a + b) = gl g a ++ (List.range' (1 + a) b).map g := by
  unfold gl
  rw [← List.map_append, show 1 + a = 1 + 1 * a by ring, List.range'_append]

theorem gl_succ (a : ℕ) : gl g (a + 1) = gl g a ++ [g (a + 1)] := by
  rw [gl_add]; simp [add_comm]

variable {g}

theorem level_sets (hg1 : g 1 = 1) (hmono : ∀ i j, 1 ≤ i → i ≤ j → g i ≤ g j)
    (hcount : ∀ n, 1 ≤ n → {j | 1 ≤ j ∧ g j = n}.ncard = g n) :
    ∀ i j, (1 ≤ j ∧ g j ≤ i) ↔ (1 ≤ j ∧ j ≤ (gl g i).sum) := by
  have hpos : ∀ j, 1 ≤ j → 1 ≤ g j := fun j hj => hg1 ▸ hmono 1 j le_rfl hj
  intro i
  induction i with
  | zero =>
    intro j
    simp only [gl, List.range'_zero, List.map_nil, List.sum_nil]
    constructor
    · rintro ⟨h1, h2⟩; have := hpos j h1; omega
    · rintro ⟨h1, h2⟩; omega
  | succ i ih =>
    have hP : (gl g (i + 1)).sum = (gl g i).sum + g (i + 1) := by
      rw [gl_succ]; simp
    have hF := interval_of_down {j | 1 ≤ j ∧ g j = i + 1} (gl g i).sum (g (i + 1))
      (hcount (i + 1) (by omega)) (hpos (i + 1) (by omega))
      (by
        rintro j ⟨h1, h2⟩
        by_contra hle
        have := ((ih j).2 ⟨h1, by omega⟩).2
        omega)
      (by
        rintro j ⟨h1, h2⟩ j' hj' hjj
        have h1' : 1 ≤ j' := by omega
        refine ⟨h1', ?_⟩
        have hle := hmono j' j h1' hjj
        have hgt : ¬ g j' ≤ i := fun h => by have := ((ih j').1 ⟨h1', h⟩).2; omega
        omega)
    intro j
    rw [hP]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rcases Nat.lt_or_ge i (g j) with hlt | hge
      · have := ((hF j).1 ⟨h1, by omega⟩).2; omega
      · have := ((ih j).1 ⟨h1, hge⟩).2; omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rcases Nat.lt_or_ge (gl g i).sum j with hlt | hge
      · have := ((hF j).2 ⟨hlt, h2⟩).2; omega
      · have := ((ih j).2 ⟨h1, hge⟩).2; omega

theorem gl_gam (hg1 : g 1 = 1) (hmono : ∀ i j, 1 ≤ i → i ≤ j → g i ≤ g j)
    (hcount : ∀ n, 1 ≤ n → {j | 1 ≤ j ∧ g j = n}.ncard = g n) (m : ℕ) :
    gam (gl g m) = gl g (gl g m).sum := by
  induction m with
  | zero => simp [gl, gam]
  | succ m ih =>
    have hL := level_sets hg1 hmono hcount
    rw [gl_succ, gam_append, ih, List.sum_append, gl_add]
    congr 1
    apply List.ext_getElem
    · simp [gl]
    · intro t h1 h2
      simp only [List.mapIdx_cons, List.mapIdx_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.getElem_replicate, List.getElem_map, List.getElem_range',
        List.length_map, List.length_range', gl] at h1 h2 ⊢
      have hP : (gl g (m + 1)).sum = (gl g m).sum + g (m + 1) := by rw [gl_succ]; simp
      have hs : [g (m + 1)].sum = g (m + 1) := by simp
      rw [hs] at h2
      have hgl : (gl g m).sum = (List.map g (List.range' 1 m)).sum := rfl
      rw [← hgl]
      have a := ((hL (m + 1) (1 + (gl g m).sum + 1 * t)).2 ⟨by omega, by rw [hP]; omega⟩).2
      have b : ¬ g (1 + (gl g m).sum + 1 * t) ≤ m := fun h => by
        have := ((hL m _).1 ⟨by omega, h⟩).2; omega
      omega

theorem gl_R (hg1 : g 1 = 1) (hmono : ∀ i j, 1 ≤ i → i ≤ j → g i ≤ g j)
    (hcount : ∀ n, 1 ≤ n → {j | 1 ≤ j ∧ g j = n}.ncard = g n) (k : ℕ) :
    gl g (R (k + 2)).length = R (k + 2) := by
  induction k with
  | zero =>
    have hL := level_sets hg1 hmono hcount
    have e2 : (gl g 2).sum = g 1 + g 2 := by
      unfold gl; rw [show List.range' 1 2 = [1, 2] from rfl]; simp
    have e1 : (gl g 1).sum = g 1 := by
      unfold gl; rw [show List.range' 1 1 = [1] from rfl]; simp
    have h2 : g 2 = 2 := by
      have := hmono 1 2 (by omega) (by omega)
      have a := ((hL 2 2).2 ⟨by omega, by rw [e2]; omega⟩).2
      have b : ¬ g 2 ≤ 1 := fun h => by have := ((hL 1 2).1 ⟨by omega, h⟩).2; omega
      omega
    rw [R_two]
    show [g 1, g 2] = [1, 2]
    rw [hg1, h2]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, R_succ (k + 2), length_gam]
    conv_rhs => rw [← ih]
    rw [gl_gam hg1 hmono hcount, ih]

/-- Any sequence satisfying the definition of A001462 (g(1) = 1, nondecreasing, every n ≥ 1
occurs exactly g(n) times) agrees with `golomb` on n ≥ 1. -/
theorem golomb_unique (hg1 : g 1 = 1) (hmono : ∀ i j, 1 ≤ i → i ≤ j → g i ≤ g j)
    (hcount : ∀ n, 1 ≤ n → {j | 1 ≤ j ∧ g j = n}.ncard = g n) (n : ℕ) (hn : 1 ≤ n) :
    g n = golomb n := by
  have hlen : n - 1 < (R (n + 2)).length := by have := length_R n; omega
  have e := gl_R hg1 hmono hcount n
  unfold golomb
  rw [List.getD_eq_getElem _ _ hlen]
  have hlen' : n - 1 < (gl g (R (n + 2)).length).length := by simp [gl]; omega
  rw [← List.getElem_of_eq e hlen']
  simp [gl]
  congr 1; omega

end unique

end OEIS_A113676

open OEIS_A113676
