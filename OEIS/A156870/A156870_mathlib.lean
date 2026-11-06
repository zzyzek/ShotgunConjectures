import Mathlib

/-
OEIS A156869: T(n,k) = number of nondecreasing sequences of n positive
integers with reciprocals adding up to k (1 <= k <= n).
OEIS A156870: a(n) = T(2n, n).
Conjecture (both entries): T(2n + m, n + m) = T(2n, n) if and only if m >= 0
(for the entries of the triangle, i.e. n + m >= 1).

Checked here (Lean 4.35.0, Mathlib):
* `A156869_conjecture`: for n ≥ 1 and an integer m with 1 ≤ n + m,
  T (2n + m) (n + m) = T (2n) n ↔ 0 ≤ m.
* `diag_const`: T (2n + m) (n + m) = T (2n) n for m : ℕ.
* `diag_lt`: T (2n - d) (n - d) < T (2n) n for 1 ≤ d < n.
T is `Set.ncard` of the set `Seqs n k` of lists (length n, pairwise ≤,
entries positive, ∑ 1/x = k in ℚ).
Route: prepending 1 maps Seqs N K into Seqs (N+1) (K+1) injectively
(`cons_mem`); it is onto when N ≤ 2K, since a list with no 1 has
∑ 1/x ≤ length/2 (`head_one`); for N = 2K - 1 the all-twos list of length
2K is missed (`step_lt`); every Seqs N K is finite (`seqs_finite`, the least
entry x of a list with sum s > 0 has x ≤ length/s).

Not checked here: nothing the statement depends on.  Agreement of `T`
with the data terms: certificate/brute.py (rows 1..6).
-/

open Finset

/-- Nondecreasing lists of n positive integers with reciprocal sum k. -/
def Seqs (n : ℕ) (k : ℚ) : Set (List ℕ) :=
  {l | l.length = n ∧ l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, 0 < x) ∧
    (l.map fun x : ℕ => (1 : ℚ) / x).sum = k}

/-- A156869. -/
noncomputable def T (n k : ℕ) : ℕ := (Seqs n k).ncard

/-- A156870. -/
noncomputable def A156870 (n : ℕ) : ℕ := T (2 * n) n

lemma recip_sum_le (c : ℕ) (hc : 0 < c) :
    ∀ l : List ℕ, (∀ y ∈ l, c ≤ y) →
      (l.map fun x : ℕ => (1 : ℚ) / x).sum ≤ l.length * ((1 : ℚ) / c) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons y t ih =>
    intro h
    have hy : c ≤ y := h y (by simp)
    have ht := ih (fun z hz => h z (by simp [hz]))
    have hc' : (0 : ℚ) < c := by exact_mod_cast hc
    have hcy : (c : ℚ) ≤ y := by exact_mod_cast hy
    have : (1 : ℚ) / y ≤ 1 / c := one_div_le_one_div_of_le hc' hcy
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

lemma recip_sum_nonneg (l : List ℕ) : 0 ≤ (l.map fun x : ℕ => (1 : ℚ) / x).sum := by
  apply List.sum_nonneg
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨x, _, rfl⟩ := hq
  positivity

lemma cons_mem {N : ℕ} {K : ℚ} {l : List ℕ} (h : l ∈ Seqs N K) :
    (1 :: l) ∈ Seqs (N + 1) (K + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [h1], ?_, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨fun y hy => h3 y hy, h2⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · norm_num
    · exact h3 x hx
  · simp only [List.map_cons, List.sum_cons, h4]
    norm_num
    ring

lemma head_one {N K : ℕ} {l : List ℕ} (h : l ∈ Seqs (N + 1) ((K : ℚ) + 1))
    (hNK : N ≤ 2 * K) : ∃ t, l = 1 :: t ∧ t ∈ Seqs N K := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  match l, h1, h2, h3, h4 with
  | x :: t, h1, h2, h3, h4 =>
    rw [List.pairwise_cons] at h2
    have hx : 0 < x := h3 x (by simp)
    by_cases hx1 : x = 1
    · subst hx1
      refine ⟨t, rfl, by simpa using h1, h2.2, fun y hy => h3 y (by simp [hy]), ?_⟩
      simp only [List.map_cons, List.sum_cons, Nat.cast_one, div_one] at h4
      linarith
    · exfalso
      have hall : ∀ y ∈ x :: t, 2 ≤ y := by
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · omega
        · have := h2.1 y hy; omega
      have := recip_sum_le 2 (by norm_num) (x :: t) hall
      rw [h4, h1] at this
      have hNK' : (N : ℚ) ≤ 2 * K := by exact_mod_cast hNK
      push_cast at this
      linarith

lemma image_eq {N K : ℕ} (hNK : N ≤ 2 * K) :
    Seqs (N + 1) ((K : ℚ) + 1) = (List.cons 1) '' Seqs N K := by
  ext l
  constructor
  · intro h
    obtain ⟨t, rfl, ht⟩ := head_one h hNK
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact cons_mem ht

lemma step_eq {N K : ℕ} (hNK : N ≤ 2 * K) : T (N + 1) (K + 1) = T N K := by
  unfold T
  push_cast
  rw [image_eq hNK, Set.ncard_image_of_injective _ (List.cons_injective)]

lemma seqs_finite : ∀ (N : ℕ) (s : ℚ), (Seqs N s).Finite := by
  intro N
  induction N with
  | zero =>
    intro s
    apply Set.Finite.subset (Set.finite_singleton ([] : List ℕ))
    intro l hl
    exact List.length_eq_zero_iff.1 hl.1
  | succ N ih =>
    intro s
    let B : ℕ := ⌈((N : ℚ) + 1) / s⌉₊
    apply Set.Finite.subset
      (Set.Finite.biUnion (Finset.range (B + 1)).finite_toSet
        (fun x _ => (ih (s - 1 / x)).image (List.cons x)))
    intro l hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    match l, h1, h2, h3, h4 with
    | x :: t, h1, h2, h3, h4 =>
      rw [List.pairwise_cons] at h2
      have hx : 0 < x := h3 x (by simp)
      have hx' : (0 : ℚ) < x := by exact_mod_cast hx
      simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨x, ?_, t, ⟨by simpa using h1, h2.2, fun y hy => h3 y (by simp [hy]), ?_⟩, rfl⟩
      · simp only [Finset.coe_range, Set.mem_Iio]
        have hall : ∀ y ∈ x :: t, x ≤ y := by
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact le_rfl
          · exact h2.1 y hy
        have hle := recip_sum_le x hx (x :: t) hall
        rw [h4, h1] at hle
        have hpos : 0 < s := by
          rw [← h4]
          simp only [List.map_cons, List.sum_cons]
          have := recip_sum_nonneg t
          have : (0 : ℚ) < 1 / x := by positivity
          linarith
        have hxs : (x : ℚ) ≤ ((N : ℚ) + 1) / s := by
          rw [le_div_iff₀ hpos]
          push_cast at hle
          have e : ((N : ℚ) + 1) * (1 / x) = ((N : ℚ) + 1) / x := by ring
          rw [e, le_div_iff₀ hx'] at hle
          linarith
        have := (Nat.le_ceil (((N : ℚ) + 1) / s))
        have hxB : (x : ℚ) ≤ (B : ℚ) := le_trans hxs this
        have : x ≤ B := by exact_mod_cast hxB
        omega
      · simp only [List.map_cons, List.sum_cons] at h4
        linarith

lemma step_le (N K : ℕ) : T N K ≤ T (N + 1) (K + 1) := by
  unfold T
  rw [← Set.ncard_image_of_injective (Seqs N K) (List.cons_injective (a := (1 : ℕ)))]
  refine Set.ncard_le_ncard ?_ (seqs_finite _ _)
  rintro _ ⟨t, ht, rfl⟩
  have := cons_mem ht
  simpa using this

lemma step_lt (J : ℕ) : T (2 * J + 1) J < T (2 * J + 2) (J + 1) := by
  unfold T
  rw [← Set.ncard_image_of_injective (Seqs (2 * J + 1) J) (List.cons_injective (a := (1 : ℕ)))]
  refine Set.ncard_lt_ncard ?_ (seqs_finite _ _)
  rw [Set.ssubset_iff_of_subset]
  · refine ⟨List.replicate (2 * J + 2) 2, ?_, ?_⟩
    · refine ⟨by simp, ?_, ?_, ?_⟩
      · rw [List.pairwise_replicate]; right; exact le_rfl
      · intro x hx
        rw [List.eq_of_mem_replicate hx]; norm_num
      · simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
        push_cast
        ring
    · rintro ⟨t, _, ht⟩
      have := congrArg List.head? ht
      simp [List.replicate_succ] at this
  · rintro _ ⟨t, ht, rfl⟩
    have := cons_mem ht
    simpa [show 2 * J + 1 + 1 = 2 * J + 2 by ring] using this

/-- The diagonals are constant from T(2n, n) on (the "if" direction). -/
theorem diag_const (n m : ℕ) : T (2 * n + m) (n + m) = T (2 * n) n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * n + (m + 1) = (2 * n + m) + 1 by ring,
      show n + (m + 1) = (n + m) + 1 by ring, step_eq (by omega), ih]

lemma chain_le (N K : ℕ) : ∀ i, T N K ≤ T (N + i) (K + i) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    exact le_trans ih (by
      rw [show N + (i + 1) = (N + i) + 1 by ring, show K + (i + 1) = (K + i) + 1 by ring]
      exact step_le _ _)

/-- Strict drop below the diagonal entry (the "only if" direction). -/
theorem diag_lt (n d : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    T (2 * n - d) (n - d) < T (2 * n) n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + d := ⟨n - d, by omega⟩
  have h1 := chain_le (2 * j + d) j (d - 1)
  have h2 := step_lt (j + d - 1)
  rw [show 2 * (j + d) - d = 2 * j + d by omega, show j + d - d = j by omega]
  rw [show 2 * j + d + (d - 1) = 2 * (j + d - 1) + 1 by omega,
    show j + (d - 1) = j + d - 1 by omega] at h1
  rw [show 2 * (j + d - 1) + 2 = 2 * (j + d) by omega,
    show j + d - 1 + 1 = j + d by omega] at h2
  omega

/-- The conjecture of A156869 / A156870. -/
theorem A156869_conjecture (n : ℕ) (m : ℤ) (hn : 1 ≤ n) (hnm : 1 ≤ (n : ℤ) + m) :
    T (2 * (n : ℤ) + m).toNat ((n : ℤ) + m).toNat = A156870 n ↔ 0 ≤ m := by
  unfold A156870
  constructor
  · intro h
    by_contra hm'
    have hm : m < 0 := not_le.mp hm'
    have hd := diag_lt n m.natAbs (by omega) (by omega)
    rw [show (2 * (n : ℤ) + m).toNat = 2 * n - m.natAbs by omega,
      show ((n : ℤ) + m).toNat = n - m.natAbs by omega] at h
    omega
  · intro hm
    have := diag_const n m.toNat
    rw [show (2 * (n : ℤ) + m).toNat = 2 * n + m.toNat by omega,
      show ((n : ℤ) + m).toNat = n + m.toNat by omega]
    exact this
