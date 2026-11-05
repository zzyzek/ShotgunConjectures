/-
OEIS A195608 and A195609 (V. Shevelev, 2011).  Shared Lean file for both
entries (OEIS/A195609/README.md points here).

A195608 lists the n ≥ 1 with Sum_{i=1..n} A(i) = A(n)·A(n+1)/4 for A = A001969
(evil numbers, offset 1, A(1) = 0); A195609 the same for A = A000069 (odious
numbers, offset 1, A(1) = 1).  The equation is stated as
4·Sum_{i=1..n} A(i) = A(n)·A(n+1) in ℕ, which is the same condition.

Definitions.
* `tm n` = (sum of the binary digits of n) mod 2, the Thue–Morse sequence.
* `evil n`   = `Nat.nth (fun k => tm k = 0) (n - 1)`, the n-th evil number.
* `odious n` = `Nat.nth (fun k => tm k = 1) (n - 1)`, the n-th odious number.
* `SumSet A` = {n | 1 ≤ n ∧ 4 * Sum_{i ∈ Icc 1 n} A i = A n * A (n+1)}.
* `A195608set = SumSet evil`, `A195609set = SumSet odious`.
`evil_values`, `odious_values`, `A195608_values`, `A195609_values` check the
definitions against the first OEIS terms by `decide`.

Main theorems (S = A195608set with s = tm, or S = A195609set with s = 1 - tm).
* closed form: n ∈ S ↔ (∃ j, n = 2j+1 ∧ s j = 0) ∨ (∃ j, n = 2j+2 ∧ s j = 0 ∧ s (j+1) = 0)
  (`A195608_closed_form`, `A195609_closed_form`).
* conjecture 1 (`*_conj1`): for n ∈ S there is d ∈ {1, 4, 6} with n + d ∈ S and
  no element of S strictly between n and n + d; `*_conj1_occur`: all three
  values occur as differences of consecutive elements.
* conjecture 2 (`*_conj2`): if [a, b] ⊆ S, a - 1 ∉ S and b + 1 ∉ S then
  b = a or b = a + 2 (every maximal run of consecutive elements has length 1 or 3).
* conjecture 3 (`*_conj3`): if m ∈ S, m - 1 ∉ S (m starts its run) and
  m ≥ 2, then A(m+1) - A(m-1) = 5.  For A195608 the run {1} has m = 1 and
  A(0) does not exist; A195609 has no element 1, so there the hypothesis
  m ≥ 2 is dropped.  `*_conj3_iff`: for m ∈ S, m ≥ 2,
  A(m+1) = A(m-1) + 5 ↔ m - 1 ∉ S.

Proof: A(k+1) = 2k + s(k), Sum_{k<2j} s(k) = j, s(2j) = s(j),
s(2j+1) = 1 - s(j), and s never takes the same value three times in a row.
All of it is proved for any s with these recursions (`TMLike`).

Not checked: nothing outside Lean.  No native_decide.
-/
import Mathlib

open Finset

/-- Thue–Morse: parity of the binary digit sum (A010060). -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).sum % 2

/-- A001969(n), offset 1: the n-th evil number (evil 1 = 0). -/
noncomputable def evil (n : ℕ) : ℕ := Nat.nth (fun k => tm k = 0) (n - 1)

/-- A000069(n), offset 1: the n-th odious number (odious 1 = 1). -/
noncomputable def odious (n : ℕ) : ℕ := Nat.nth (fun k => tm k = 1) (n - 1)

/-- {n ≥ 1 : Sum_{i=1..n} A(i) = A(n) A(n+1) / 4}. -/
def SumSet (A : ℕ → ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ 4 * ∑ i ∈ Icc 1 n, A i = A n * A (n + 1)}

def A195608set : Set ℕ := SumSet evil
def A195609set : Set ℕ := SumSet odious

lemma tm_le (n : ℕ) : tm n ≤ 1 := by
  unfold tm; omega

lemma tm_even (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tm]
  · unfold tm
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]

lemma tm_odd (n : ℕ) : tm (2 * n + 1) = 1 - tm n := by
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2, List.sum_cons]
  omega

/-- A 0/1 sequence with the Thue–Morse recursions (tm or 1 - tm). -/
structure TMLike (s : ℕ → ℕ) : Prop where
  even : ∀ n, s (2 * n) = s n
  odd : ∀ n, s (2 * n + 1) = 1 - s n
  le : ∀ n, s n ≤ 1

/-- The sequence 2(n-1) + s(n-1): the n-th zero of s, see `nth_eq`. -/
def seqOf (s : ℕ → ℕ) (n : ℕ) : ℕ := 2 * (n - 1) + s (n - 1)

lemma seqOf_succ (s : ℕ → ℕ) (n : ℕ) : seqOf s (n + 1) = 2 * n + s n := by
  simp [seqOf]

variable {s : ℕ → ℕ}

lemma TMLike.cases (h : TMLike s) (n : ℕ) : s n = 0 ∨ s n = 1 := by
  have := h.le n; omega

lemma TMLike.no_three (h : TMLike s) (j : ℕ) : ¬ (s j = s (j + 1) ∧ s (j + 1) = s (j + 2)) := by
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · have e := h.even i; have o := h.odd i; have l := h.le i
    omega
  · have e := h.even (i + 1); have o := h.odd (i + 1); have l := h.le (i + 1)
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring]
    omega

lemma TMLike.count_even (h : TMLike s) (j : ℕ) : Nat.count (fun i => s i = 0) (2 * j) = j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, ih,
      h.odd, h.even]
    rcases h.cases j with hj | hj <;> simp [hj]

/-- The k-th zero of s (from 0) is 2k + s(k). -/
lemma TMLike.nth_eq (h : TMLike s) (k : ℕ) : Nat.nth (fun i => s i = 0) k = 2 * k + s k := by
  have hp : s (2 * k + s k) = 0 := by
    rcases h.cases k with hk | hk
    · rw [hk, add_zero, h.even, hk]
    · rw [hk, h.odd, hk]
  have hc : Nat.count (fun i => s i = 0) (2 * k + s k) = k := by
    rcases h.cases k with hk | hk
    · rw [hk, add_zero, h.count_even]
    · rw [hk, Nat.count_succ, h.count_even, h.even, hk]; simp
  have := Nat.nth_count (p := fun i => s i = 0) hp
  rw [hc] at this
  exact this

lemma sum_seqOf (n : ℕ) : ∑ i ∈ Icc 1 n, seqOf s i = ∑ k ∈ range n, (2 * k + s k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, seqOf_succ]

lemma TMLike.F_even (h : TMLike s) (j : ℕ) : ∑ k ∈ range (2 * j), (2 * k + s k) + j = 4 * j * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ, h.even, h.odd]
    rcases h.cases j with hj | hj <;> rw [hj] <;> ring_nf <;> ring_nf at ih <;> omega

lemma TMLike.mem_odd (h : TMLike s) (j : ℕ) : 2 * j + 1 ∈ SumSet (seqOf s) ↔ s j = 0 := by
  simp only [SumSet, Set.mem_ofPred_eq]
  rw [sum_seqOf, sum_range_succ, seqOf_succ, seqOf_succ, h.even, h.odd]
  have FE := h.F_even j
  generalize ∑ k ∈ range (2 * j), (2 * k + s k) = X at FE ⊢
  rcases h.cases j with hj | hj <;> rw [hj] <;> simp <;> ring_nf <;> ring_nf at FE <;> omega

lemma TMLike.mem_even (h : TMLike s) (j : ℕ) :
    2 * j + 2 ∈ SumSet (seqOf s) ↔ s j = 0 ∧ s (j + 1) = 0 := by
  have e1 : seqOf s (2 * j + 2) = 2 * (2 * j + 1) + (1 - s j) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, seqOf_succ, h.odd]
  have e2 : seqOf s (2 * j + 2 + 1) = 2 * (2 * j + 2) + s (j + 1) := by
    rw [seqOf_succ, show 2 * j + 2 = 2 * (j + 1) by ring, h.even]
  have FE := h.F_even (j + 1)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at FE
  simp only [SumSet, Set.mem_ofPred_eq]
  rw [sum_seqOf, e1, e2]
  generalize ∑ k ∈ range (2 * j + 2), (2 * k + s k) = X at FE ⊢
  rcases h.cases j with ha | ha <;> rcases h.cases (j + 1) with hb | hb <;> rw [ha, hb] <;>
    simp <;> ring_nf <;> ring_nf at FE <;> omega

lemma seqOf_zero_not_mem : 0 ∉ SumSet (seqOf s) := by
  simp [SumSet]

/-- Closed form of S. -/
lemma TMLike.mem_iff (h : TMLike s) (n : ℕ) : n ∈ SumSet (seqOf s) ↔
    (∃ j, n = 2 * j + 1 ∧ s j = 0) ∨ (∃ j, n = 2 * j + 2 ∧ s j = 0 ∧ s (j + 1) = 0) := by
  constructor
  · intro hn
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd hn seqOf_zero_not_mem
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [show 2 * (i + 1) = 2 * i + 2 by ring, h.mem_even] at hn
        exact Or.inr ⟨i, by ring, hn⟩
    · exact Or.inl ⟨j, rfl, (h.mem_odd j).1 hn⟩
  · rintro (⟨j, rfl, hj⟩ | ⟨j, rfl, hj⟩)
    · exact (h.mem_odd j).2 hj
    · exact (h.mem_even j).2 hj

/-- Decidable form of the closed form (used for the value checks). -/
lemma TMLike.mem_iff_dec (h : TMLike s) (n : ℕ) : n ∈ SumSet (seqOf s) ↔
    (n % 2 = 1 ∧ s (n / 2) = 0) ∨ (n % 2 = 0 ∧ 2 ≤ n ∧ s (n / 2 - 1) = 0 ∧ s (n / 2) = 0) := by
  rw [h.mem_iff]
  constructor
  · rintro (⟨j, rfl, hj⟩ | ⟨j, rfl, hj, hj1⟩)
    · exact Or.inl ⟨by omega, by rw [show (2 * j + 1) / 2 = j by omega]; exact hj⟩
    · refine Or.inr ⟨by omega, by omega, ?_, ?_⟩
      · rw [show (2 * j + 2) / 2 - 1 = j by omega]; exact hj
      · rw [show (2 * j + 2) / 2 = j + 1 by omega]; exact hj1
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨n / 2, by omega, h2⟩
    · exact Or.inr ⟨n / 2 - 1, by omega, h3, by rw [show n / 2 - 1 + 1 = n / 2 by omega]; exact h4⟩

/-- Conjecture 1: the next element after n is n + 1, n + 4 or n + 6. -/
lemma TMLike.gaps (h : TMLike s) (n : ℕ) (hn : n ∈ SumSet (seqOf s)) :
    ∃ d ∈ ({1, 4, 6} : Finset ℕ), n + d ∈ SumSet (seqOf s) ∧
      ∀ k, n < k → k < n + d → k ∉ SumSet (seqOf s) := by
  rw [h.mem_iff] at hn
  rcases hn with ⟨j, rfl, hj⟩ | ⟨j, rfl, hj, hj1⟩
  · rcases h.cases (j + 1) with h1 | h1
    · refine ⟨1, by simp, (h.mem_even j).2 ⟨hj, h1⟩, fun k hk1 hk2 => by omega⟩
    rcases h.cases (j + 2) with h2 | h2
    · refine ⟨4, by simp, ?_, ?_⟩
      · rw [show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring]; exact (h.mem_odd _).2 h2
      · intro k hk1 hk2 hk
        rcases (show k = 2 * j + 2 ∨ k = 2 * (j + 1) + 1 ∨ k = 2 * (j + 1) + 2 by omega)
          with rfl | rfl | rfl
        · have := (h.mem_even j).1 hk; omega
        · have := (h.mem_odd (j + 1)).1 hk; omega
        · have := (h.mem_even (j + 1)).1 hk; omega
    have h3 : s (j + 3) = 0 := by
      have := h.no_three (j + 1); have := h.cases (j + 3)
      rw [show j + 1 + 1 = j + 2 by ring, show j + 1 + 2 = j + 3 by ring] at *
      omega
    refine ⟨6, by simp, ?_, ?_⟩
    · rw [show 2 * j + 1 + 6 = 2 * (j + 3) + 1 by ring]; exact (h.mem_odd _).2 h3
    · intro k hk1 hk2 hk
      rcases (show k = 2 * j + 2 ∨ k = 2 * (j + 1) + 1 ∨ k = 2 * (j + 1) + 2 ∨
          k = 2 * (j + 2) + 1 ∨ k = 2 * (j + 2) + 2 by omega) with rfl | rfl | rfl | rfl | rfl
      · have := (h.mem_even j).1 hk; omega
      · have := (h.mem_odd (j + 1)).1 hk; omega
      · have := (h.mem_even (j + 1)).1 hk; omega
      · have := (h.mem_odd (j + 2)).1 hk; omega
      · have := (h.mem_even (j + 2)).1 hk; omega
  · refine ⟨1, by simp, ?_, fun k hk1 hk2 => by omega⟩
    rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring]; exact (h.mem_odd _).2 hj1

/-- Conjecture 2: maximal runs of consecutive elements have length 1 or 3. -/
lemma TMLike.runs (h : TMLike s) (a b : ℕ) (hab : a ≤ b)
    (hin : ∀ k, a ≤ k → k ≤ b → k ∈ SumSet (seqOf s))
    (ha : a - 1 ∉ SumSet (seqOf s)) (hb : b + 1 ∉ SumSet (seqOf s)) :
    b = a ∨ b = a + 2 := by
  by_contra hne
  have h0 := hin a le_rfl hab
  have h1 := hin (a + 1) (by omega) (by omega)
  rcases Nat.even_or_odd' a with ⟨i, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact seqOf_zero_not_mem h0
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, h.mem_even] at h0
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, h.mem_odd] at ha
    exact ha h0.1
  · rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, h.mem_even] at h1
    have h2 : 2 * i + 1 + 2 ∈ SumSet (seqOf s) := by
      rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring]; exact (h.mem_odd _).2 h1.2
    have h3 : 2 * i + 1 + 3 ∉ SumSet (seqOf s) := by
      rw [show 2 * i + 1 + 3 = 2 * (i + 1) + 2 by ring, h.mem_even, show i + 1 + 1 = i + 2 by ring]
      have := h.no_three i
      omega
    rcases (show b = 2 * i + 1 + 1 ∨ 2 * i + 1 + 3 ≤ b by omega) with rfl | hb3
    · exact hb h2
    · exact h3 (hin _ (by omega) hb3)

/-- Conjecture 3 (sharpened): for m ∈ S, m ≥ 2, A(m+1) = A(m-1) + 5 iff m starts its run. -/
lemma TMLike.run_start (h : TMLike s) (m : ℕ) (hm : m ∈ SumSet (seqOf s)) (h2 : 2 ≤ m) :
    seqOf s (m + 1) = seqOf s (m - 1) + 5 ↔ m - 1 ∉ SumSet (seqOf s) := by
  rw [h.mem_iff] at hm
  rcases hm with ⟨j, rfl, hj⟩ | ⟨j, rfl, hj, hj1⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have A1 : seqOf s (2 * (i + 1) + 1 + 1) = 2 * (2 * (i + 1) + 1) + (1 - s (i + 1)) := by
      rw [seqOf_succ, h.odd]
    have A2 : seqOf s (2 * (i + 1) + 1 - 1) = 2 * (2 * i + 1) + (1 - s i) := by
      rw [show 2 * (i + 1) + 1 - 1 = (2 * i + 1) + 1 by omega, seqOf_succ, h.odd]
    have M : 2 * (i + 1) + 1 - 1 ∈ SumSet (seqOf s) ↔ s i = 0 ∧ s (i + 1) = 0 := by
      rw [show 2 * (i + 1) + 1 - 1 = 2 * i + 2 by omega]; exact h.mem_even i
    rw [A1, A2, M]
    have := h.le i
    constructor <;> intro H <;> omega
  · have A1 : seqOf s (2 * j + 2 + 1) = 2 * (2 * j + 2) + s (j + 1) := by
      rw [seqOf_succ, show 2 * j + 2 = 2 * (j + 1) by ring, h.even]
    have A2 : seqOf s (2 * j + 2 - 1) = 2 * (2 * j) + s j := by
      rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega, seqOf_succ, h.even]
    have M : 2 * j + 2 - 1 ∈ SumSet (seqOf s) := by
      rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega]; exact (h.mem_odd j).2 hj
    rw [A1, A2]
    constructor
    · intro H; omega
    · intro H; exact absurd M H

lemma tm_like : TMLike tm := ⟨tm_even, tm_odd, tm_le⟩

lemma ntm_like : TMLike (fun n => 1 - tm n) :=
  ⟨fun n => by simp [tm_even], fun n => by simp [tm_odd],
    fun n => by omega⟩

/-- A001969(n) = 2(n-1) + t(n-1). -/
lemma evil_eq : evil = seqOf tm := by
  funext n
  unfold evil seqOf
  exact tm_like.nth_eq (n - 1)

/-- A000069(n) = 2(n-1) + 1 - t(n-1). -/
lemma odious_eq : odious = seqOf (fun n => 1 - tm n) := by
  funext n
  have hp : (fun k => tm k = 1) = (fun k => 1 - tm k = 0) := by
    funext k; have := tm_le k; apply propext; omega
  unfold odious seqOf
  rw [hp]
  exact ntm_like.nth_eq (n - 1)

lemma A195608set_eq : A195608set = SumSet (seqOf tm) := by
  rw [A195608set, evil_eq]

lemma A195609set_eq : A195609set = SumSet (seqOf (fun n => 1 - tm n)) := by
  rw [A195609set, odious_eq]

/-! Checks of the definitions against OEIS data. -/

theorem evil_values : (List.range 20).map (fun n => evil (n + 1)) =
    [0, 3, 5, 6, 9, 10, 12, 15, 17, 18, 20, 23, 24, 27, 29, 30, 33, 34, 36, 39] := by
  rw [evil_eq]; decide

theorem odious_values : (List.range 20).map (fun n => odious (n + 1)) =
    [1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31, 32, 35, 37, 38] := by
  rw [odious_eq]; decide

theorem A195608_values : ∀ n, n < 50 →
    (n ∈ A195608set ↔ n ∈ [1, 7, 11, 12, 13, 19, 20, 21, 25, 31, 35, 36, 37, 41, 47, 48, 49]) := by
  intro n hn
  rw [A195608set_eq, tm_like.mem_iff_dec]
  revert n; decide

theorem A195609_values : ∀ n, n < 50 →
    (n ∈ A195609set ↔ n ∈ [3, 4, 5, 9, 15, 16, 17, 23, 27, 28, 29, 33, 39, 43, 44, 45]) := by
  intro n hn
  rw [A195609set_eq, ntm_like.mem_iff_dec]
  revert n; decide

/-! A195608 (evil numbers). -/

theorem A195608_closed_form (n : ℕ) : n ∈ A195608set ↔
    (∃ j, n = 2 * j + 1 ∧ tm j = 0) ∨ (∃ j, n = 2 * j + 2 ∧ tm j = 0 ∧ tm (j + 1) = 0) := by
  rw [A195608set_eq]; exact tm_like.mem_iff n

theorem A195608_conj1 (n : ℕ) (hn : n ∈ A195608set) :
    ∃ d ∈ ({1, 4, 6} : Finset ℕ), n + d ∈ A195608set ∧
      ∀ k, n < k → k < n + d → k ∉ A195608set := by
  rw [A195608set_eq] at *; exact tm_like.gaps n hn

theorem A195608_conj2 (a b : ℕ) (hab : a ≤ b) (hin : ∀ k, a ≤ k → k ≤ b → k ∈ A195608set)
    (ha : a - 1 ∉ A195608set) (hb : b + 1 ∉ A195608set) : b = a ∨ b = a + 2 := by
  rw [A195608set_eq] at *; exact tm_like.runs a b hab hin ha hb

theorem A195608_conj3_iff (m : ℕ) (hm : m ∈ A195608set) (h2 : 2 ≤ m) :
    evil (m + 1) = evil (m - 1) + 5 ↔ m - 1 ∉ A195608set := by
  rw [A195608set_eq] at *; rw [evil_eq]; exact tm_like.run_start m hm h2

theorem A195608_conj3 (m : ℕ) (hm : m ∈ A195608set) (h2 : 2 ≤ m) (hstart : m - 1 ∉ A195608set) :
    evil (m + 1) - evil (m - 1) = 5 := by
  have := (A195608_conj3_iff m hm h2).2 hstart; omega

/-- Differences 6, 4, 1 occur: 1 → 7, 7 → 11, 11 → 12. -/
theorem A195608_conj1_occur :
    (1 ∈ A195608set ∧ 7 ∈ A195608set ∧ ∀ k, 1 < k → k < 7 → k ∉ A195608set) ∧
    (7 ∈ A195608set ∧ 11 ∈ A195608set ∧ ∀ k, 7 < k → k < 11 → k ∉ A195608set) ∧
    (11 ∈ A195608set ∧ 12 ∈ A195608set) := by
  have V := A195608_values
  refine ⟨⟨(V 1 (by norm_num)).2 (by simp), (V 7 (by norm_num)).2 (by simp), ?_⟩,
    ⟨(V 7 (by norm_num)).2 (by simp), (V 11 (by norm_num)).2 (by simp), ?_⟩,
    (V 11 (by norm_num)).2 (by simp), (V 12 (by norm_num)).2 (by simp)⟩
  · intro k h1 h2 hk; rw [V k (by omega)] at hk; interval_cases k <;> simp at hk
  · intro k h1 h2 hk; rw [V k (by omega)] at hk; interval_cases k <;> simp at hk

/-! A195609 (odious numbers). -/

theorem A195609_closed_form (n : ℕ) : n ∈ A195609set ↔
    (∃ j, n = 2 * j + 1 ∧ tm j = 1) ∨ (∃ j, n = 2 * j + 2 ∧ tm j = 1 ∧ tm (j + 1) = 1) := by
  rw [A195609set_eq, ntm_like.mem_iff n]
  have := tm_le
  constructor
  · rintro (⟨j, rfl, hj⟩ | ⟨j, rfl, hj, hj1⟩)
    · exact Or.inl ⟨j, rfl, by have := this j; omega⟩
    · exact Or.inr ⟨j, rfl, by have := this j; omega, by have := this (j + 1); omega⟩
  · rintro (⟨j, rfl, hj⟩ | ⟨j, rfl, hj, hj1⟩)
    · exact Or.inl ⟨j, rfl, by simp [hj]⟩
    · exact Or.inr ⟨j, rfl, by simp [hj], by simp [hj1]⟩

theorem A195609_conj1 (n : ℕ) (hn : n ∈ A195609set) :
    ∃ d ∈ ({1, 4, 6} : Finset ℕ), n + d ∈ A195609set ∧
      ∀ k, n < k → k < n + d → k ∉ A195609set := by
  rw [A195609set_eq] at *; exact ntm_like.gaps n hn

theorem A195609_conj2 (a b : ℕ) (hab : a ≤ b) (hin : ∀ k, a ≤ k → k ≤ b → k ∈ A195609set)
    (ha : a - 1 ∉ A195609set) (hb : b + 1 ∉ A195609set) : b = a ∨ b = a + 2 := by
  rw [A195609set_eq] at *; exact ntm_like.runs a b hab hin ha hb

lemma A195609_two_le (m : ℕ) (hm : m ∈ A195609set) : 2 ≤ m := by
  by_contra h
  interval_cases m
  · exact absurd ((A195609_values 0 (by norm_num)).1 hm) (by simp)
  · exact absurd ((A195609_values 1 (by norm_num)).1 hm) (by simp)

theorem A195609_conj3_iff (m : ℕ) (hm : m ∈ A195609set) :
    odious (m + 1) = odious (m - 1) + 5 ↔ m - 1 ∉ A195609set := by
  have h2 := A195609_two_le m hm
  rw [A195609set_eq] at *; rw [odious_eq]; exact ntm_like.run_start m hm h2

theorem A195609_conj3 (m : ℕ) (hm : m ∈ A195609set) (hstart : m - 1 ∉ A195609set) :
    odious (m + 1) - odious (m - 1) = 5 := by
  have := (A195609_conj3_iff m hm).2 hstart; omega

/-- Differences 6, 4, 1 occur: 17 → 23, 5 → 9, 3 → 4. -/
theorem A195609_conj1_occur :
    (17 ∈ A195609set ∧ 23 ∈ A195609set ∧ ∀ k, 17 < k → k < 23 → k ∉ A195609set) ∧
    (5 ∈ A195609set ∧ 9 ∈ A195609set ∧ ∀ k, 5 < k → k < 9 → k ∉ A195609set) ∧
    (3 ∈ A195609set ∧ 4 ∈ A195609set) := by
  have V := A195609_values
  refine ⟨⟨(V 17 (by norm_num)).2 (by simp), (V 23 (by norm_num)).2 (by simp), ?_⟩,
    ⟨(V 5 (by norm_num)).2 (by simp), (V 9 (by norm_num)).2 (by simp), ?_⟩,
    (V 3 (by norm_num)).2 (by simp), (V 4 (by norm_num)).2 (by simp)⟩
  · intro k h1 h2 hk; rw [V k (by omega)] at hk; interval_cases k <;> simp at hk
  · intro k h1 h2 hk; rw [V k (by omega)] at hk; interval_cases k <;> simp at hk
