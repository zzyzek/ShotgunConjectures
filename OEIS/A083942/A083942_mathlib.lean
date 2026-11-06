import Mathlib

/-
OEIS A083942: positions of the breadth-first encodings (A002542) of the
complete binary trees (A084107) in A014486.
A014486 lists, in increasing order and with offset 0, the totally balanced
numbers: the binary expansion has as many 0's as 1's and, read from the most
significant bit, no prefix has more 0's than 1's (0 is the empty word).
The breadth-first code of the complete binary tree with 2^n - 1 internal
nodes is 1^s 0^s in binary, s = 2^n - 1, i.e. (2^s - 1) * 2^s
(A002542: 2^(2^n-2) - 2^(2^(n-1)-1), one index up).
Conjecture (A. Adamchuk, in the entry): a(n) = Sum_{k=1..2^n-1} A000108(k).

Checked here (Lean 4.35.0, Mathlib):
* `A083942_conjecture`: A083942 n = ∑ k ∈ Icc 1 (2^n - 1), catalan k, where
  `A083942 n` is the number of totally balanced x below (2^s - 1) 2^s
  (its position in A014486, offset 0).
* `code_balanced`: (2^s - 1) 2^s is totally balanced (it is a term of A014486).
* `count_below_code`: the same count for every s: ∑_{k=1..s} catalan k.
Route: totally balanced numbers are exactly the values of Mathlib's
`DyckWord`s read as binary (U = 1, most significant first), injectively
(`toSteps_bval`, `bval_toSteps`); a word of semilength k has value in
[2^(2k-1), (2^k - 1) 2^k] (`bval_le`, `bval_ge`), and the value (2^s - 1) 2^s
is reached only by U^s D^s (`bval_pmax`); Mathlib's
`DyckWord.card_dyckWord_semilength_eq_catalan` counts each semilength.

Not checked here: nothing the statement depends on.
-/

open DyckStep Finset

/-- U ↦ 1, D ↦ 0. -/
def bit (s : DyckStep) : ℕ := if s = U then 1 else 0

/-- 1 ↦ U, anything else ↦ D. -/
def stepOf (b : ℕ) : DyckStep := if b = 1 then U else D

/-- The binary expansion of x, most significant bit first, as steps. -/
def toSteps (x : ℕ) : List DyckStep := ((Nat.digits 2 x).reverse).map stepOf

/-- x is a term of A014486. -/
def TotBal (x : ℕ) : Prop :=
  (toSteps x).count U = (toSteps x).count D ∧
    ∀ i, ((toSteps x).take i).count D ≤ ((toSteps x).take i).count U

/-- The breadth-first code of the complete binary tree with s internal nodes:
1^s 0^s in binary. -/
def code (s : ℕ) : ℕ := (2 ^ s - 1) * 2 ^ s

open Classical in
/-- A083942: position (offset 0) of code (2^n - 1) in A014486. -/
noncomputable def A083942 (n : ℕ) : ℕ :=
  ((range (code (2 ^ n - 1))).filter TotBal).card

/-- Value of a step list read as binary, most significant first. -/
def bval : List DyckStep → ℕ
  | [] => 0
  | s :: t => bit s * 2 ^ t.length + bval t

lemma bit_le (s : DyckStep) : bit s ≤ 1 := by unfold bit; split <;> omega

lemma stepOf_bit (s : DyckStep) : stepOf (bit s) = s := by
  cases s <;> simp [stepOf, bit]

lemma bit_stepOf (d : ℕ) (h : d < 2) : bit (stepOf d) = d := by
  unfold stepOf bit
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp

lemma bval_eq_ofDigits (L : List DyckStep) :
    bval L = Nat.ofDigits 2 (L.map bit).reverse := by
  induction L with
  | nil => simp [bval]
  | cons s t ih =>
    simp only [bval, List.map_cons, List.reverse_cons, Nat.ofDigits_append,
      List.length_reverse, List.length_map, Nat.ofDigits_singleton, ih]
    ring

lemma toSteps_bval (p : DyckWord) : toSteps (bval p.toList) = p.toList := by
  unfold toSteps
  rw [bval_eq_ofDigits, Nat.digits_ofDigits 2 (by norm_num)]
  · rw [List.reverse_reverse, List.map_map]
    conv_rhs => rw [← List.map_id p.toList]
    apply List.map_congr_left
    intro s _
    exact stepOf_bit s
  · intro l hl
    simp only [List.mem_reverse, List.mem_map] at hl
    obtain ⟨s, _, rfl⟩ := hl
    have := bit_le s; omega
  · intro h
    rw [List.getLast_reverse]
    have hne : p.toList ≠ [] := by
      intro h0; apply h; simp [h0]
    simp only [List.head_map]
    rw [DyckWord.head_eq_U p hne]
    simp [bit]

lemma bval_toSteps (x : ℕ) : bval (toSteps x) = x := by
  rw [bval_eq_ofDigits]
  unfold toSteps
  rw [List.map_map]
  have : (Nat.digits 2 x).reverse.map (bit ∘ stepOf) = (Nat.digits 2 x).reverse := by
    conv_rhs => rw [← List.map_id (Nat.digits 2 x).reverse]
    apply List.map_congr_left
    intro d hd
    rw [List.mem_reverse] at hd
    exact bit_stepOf d (Nat.digits_lt_base (by norm_num) hd)
  rw [this, List.reverse_reverse, Nat.ofDigits_digits]

lemma bval_inj {p q : DyckWord} (h : bval p.toList = bval q.toList) : p = q := by
  apply DyckWord.ext
  rw [← toSteps_bval p, ← toSteps_bval q, h]

lemma balanced_val (p : DyckWord) : TotBal (bval p.toList) := by
  unfold TotBal
  rw [toSteps_bval]
  exact ⟨p.count_U_eq_count_D, p.count_D_le_count_U⟩

/-- The Dyck word of a balanced number. -/
def ofBal (x : ℕ) (h : TotBal x) : DyckWord := ⟨toSteps x, h.1, h.2⟩

lemma bval_lt (L : List DyckStep) : bval L < 2 ^ L.length := by
  induction L with
  | nil => simp [bval]
  | cons s t ih =>
    simp only [bval, List.length_cons, pow_succ]
    have := bit_le s
    have : bit s * 2 ^ t.length ≤ 2 ^ t.length := by nlinarith
    omega

lemma bval_le (L : List DyckStep) :
    bval L ≤ (2 ^ (L.count U) - 1) * 2 ^ (L.length - L.count U) := by
  induction L with
  | nil => simp [bval]
  | cons s t ih =>
    have hc : t.count U ≤ t.length := List.count_le_length
    obtain ⟨r, hr⟩ : ∃ r, t.length = t.count U + r := ⟨t.length - t.count U, by omega⟩
    have hA : 1 ≤ 2 ^ t.count U := Nat.one_le_two_pow
    cases s with
    | U =>
      simp only [bval, bit, ↓reduceIte, List.count_cons_self, List.length_cons]
      rw [show t.length + 1 - (t.count U + 1) = r by omega]
      rw [show t.length - t.count U = r by omega] at ih
      rw [hr, pow_add, pow_succ]
      zify [hA, show 1 ≤ 2 ^ t.count U * 2 from by omega] at ih ⊢
      nlinarith
    | D =>
      simp only [bval, bit, List.count_cons, List.length_cons]
      simp
      calc bval t ≤ (2 ^ t.count U - 1) * 2 ^ (t.length - t.count U) := ih
        _ ≤ (2 ^ t.count U - 1) * 2 ^ (t.length + 1 - t.count U) := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma len_count (p : DyckWord) :
    p.toList.length = 2 * p.semilength ∧ p.toList.count U = p.semilength :=
  ⟨p.two_mul_semilength_eq_length.symm, rfl⟩

lemma bval_le_word (p : DyckWord) :
    bval p.toList ≤ (2 ^ p.semilength - 1) * 2 ^ p.semilength := by
  have := bval_le p.toList
  obtain ⟨h1, h2⟩ := len_count p
  rw [h1, h2, show 2 * p.semilength - p.semilength = p.semilength by omega] at this
  exact this

lemma bval_ge (p : DyckWord) (hp : p ≠ 0) :
    2 ^ (2 * p.semilength - 1) ≤ bval p.toList := by
  have hne : p.toList ≠ [] := by
    intro h0; apply hp; exact (DyckWord.toList_eq_nil).1 h0
  obtain ⟨s, t, hst⟩ := List.exists_cons_of_ne_nil hne
  have hU : s = U := by
    have := DyckWord.head_eq_U p hne
    simp only [hst, List.head_cons] at this
    exact this
  have hlen := (len_count p).1
  rw [hst] at hlen ⊢
  subst hU
  simp only [List.length_cons] at hlen
  simp only [bval, bit, ↓reduceIte]
  rw [show 2 * p.semilength - 1 = t.length by omega]
  omega

lemma bval_append_D (L : List DyckStep) : bval (L ++ [D]) = 2 * bval L := by
  induction L with
  | nil => simp [bval, bit]
  | cons s t ih =>
    simp only [List.cons_append, bval, List.length_append, List.length_singleton, ih]
    ring

/-- U^s D^s. -/
def pmax : ℕ → DyckWord
  | 0 => 0
  | s + 1 => (pmax s).nest

lemma pmax_semilength (s : ℕ) : (pmax s).semilength = s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [pmax, ih]

lemma bval_pmax (s : ℕ) : bval (pmax s).toList = code s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hlen := (len_count (pmax s)).1
    rw [pmax_semilength] at hlen
    have e : (pmax (s + 1)).toList = U :: ((pmax s).toList ++ [D]) := by
      simp [pmax, DyckWord.nest]
    rw [e, bval, bval_append_D, ih, List.length_append, hlen]
    simp only [bit, ↓reduceIte, List.length_singleton, one_mul, code]
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
    zify [h1, h2]
    ring

lemma code_mono {k s : ℕ} (h : k ≤ s) : code k ≤ code s := by
  unfold code
  apply Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1)
    (Nat.pow_le_pow_right (by norm_num) h)

lemma code_lt_pow (s : ℕ) : code s < 2 ^ (2 * s + 1) := by
  unfold code
  have : 2 ^ (2 * s + 1) = 2 ^ s * 2 ^ s * 2 := by ring
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  rw [this]
  have : (2 ^ s - 1) * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  nlinarith

/-- Dyck words of semilength k, as a finset. -/
noncomputable def words (k : ℕ) : Finset DyckWord :=
  (univ : Finset { p : DyckWord // p.semilength = k }).map (Function.Embedding.subtype _)

lemma mem_words {k : ℕ} {p : DyckWord} : p ∈ words k ↔ p.semilength = k := by
  simp [words]

lemma card_words (k : ℕ) : (words k).card = catalan k := by
  rw [words, card_map, card_univ, DyckWord.card_dyckWord_semilength_eq_catalan]

/-- Dyck words of semilength at most s. -/
noncomputable def upTo (s : ℕ) : Finset DyckWord := (range (s + 1)).biUnion words

lemma mem_upTo {s : ℕ} {p : DyckWord} : p ∈ upTo s ↔ p.semilength ≤ s := by
  simp [upTo, mem_words]

lemma card_upTo (s : ℕ) : (upTo s).card = ∑ k ∈ range (s + 1), catalan k := by
  rw [upTo, card_biUnion]
  · simp [card_words]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hi hj
    rw [mem_words] at hi hj
    exact hij (hi.symm.trans hj)

open Classical in
lemma filter_code (s : ℕ) :
    (range (code s)).filter TotBal = ((upTo s).erase (pmax s)).image (fun p => bval p.toList) := by
  ext x
  simp only [mem_filter, mem_range, mem_image, mem_erase, mem_upTo]
  constructor
  · rintro ⟨hx, hb⟩
    refine ⟨ofBal x hb, ⟨?_, ?_⟩, bval_toSteps x⟩
    · intro h
      have := congrArg (fun p : DyckWord => bval p.toList) h
      simp only [ofBal, bval_toSteps, bval_pmax] at this
      omega
    · by_contra hk
      rw [not_le] at hk
      have hne : ofBal x hb ≠ 0 := by
        intro h0
        rw [h0] at hk
        simp at hk
      have h1 := bval_ge (ofBal x hb) hne
      simp only [ofBal, bval_toSteps] at h1
      have h2 : 2 ^ (2 * s + 1) ≤ 2 ^ (2 * (ofBal x hb).semilength - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have := code_lt_pow s
      simp only [ofBal] at h2
      omega
  · rintro ⟨p, ⟨hp, hk⟩, rfl⟩
    refine ⟨?_, balanced_val p⟩
    have h1 := bval_le_word p
    have h2 := code_mono hk
    have h3 : bval p.toList ≠ code s := by
      intro h
      rw [← bval_pmax] at h
      exact hp (bval_inj h)
    unfold code at h2 h3 ⊢
    omega

open Classical in
/-- The number of terms of A014486 below (2^s - 1) 2^s. -/
theorem count_below_code (s : ℕ) :
    ((range (code s)).filter TotBal).card = ∑ k ∈ Icc 1 s, catalan k := by
  classical
  rw [filter_code, card_image_of_injective _ (fun p q h => bval_inj h),
    card_erase_of_mem (mem_upTo.2 (by rw [pmax_semilength])), card_upTo,
    Finset.sum_range_succ', catalan_zero]
  rw [Nat.add_sub_cancel]
  rw [Finset.sum_bij (fun k _ => k + 1)]
  · intro k hk; simp at hk ⊢; omega
  · intro a _ b _ h; omega
  · intro b hb
    simp at hb
    exact ⟨b - 1, by simp; omega, by omega⟩
  · intro k _; rfl

theorem code_balanced (s : ℕ) : TotBal (code s) := by
  rw [← bval_pmax]; exact balanced_val _

/-- Adamchuk's conjecture in A083942. -/
theorem A083942_conjecture (n : ℕ) :
    A083942 n = ∑ k ∈ Icc 1 (2 ^ n - 1), catalan k := by
  unfold A083942
  convert count_below_code (2 ^ n - 1)
