/-
OEIS A212652: a(n) is the least positive integer M such that n = T(M) - T(k)
for an integer k with 0 <= k <= M, T(r) = A000217(r) = r(r+1)/2.
Conjectures (scan record, from the A209260 and A212652 entries):
* a(n) = min of d + (h-1)/2 over factorisations n = d*h with h odd.
* n appears in row a(n) of A209260, and in row d + (h-1)/2 of A141419
  for every such factorisation.

Definitions.
* `T r = r * (r + 1) / 2` (A000217).
* `a n = Nat.find (exists_rep n)`, the least M ≥ 1 with ∃ k ≤ M,
  n = T M - T k (for n ≥ 1; `a 0` is not part of the sequence).
* `row141419 r` = {T r - T (r - k) : 1 ≤ k ≤ r}  (A141419, row r).
* `row209260 r` = elements of `row141419 r` in no earlier row of A141419
  (the row construction stated in A209260).

Main theorems.
* `A212652_formula`: for n ≥ 1, a n ≤ n/h + (h-1)/2 for every odd h ∣ n,
  with equality for some odd h ∣ n.
* `mem_row141419_iff`: for n ≥ 1, n ∈ row141419 M ↔ M = n/h + (h-1)/2
  for some odd h ∣ n.
* `A212652_row209260`: for n ≥ 1, n ∈ row209260 (a n), and
  n ∈ row209260 r → r = a n.
* `A212652_consecutive`: a n is the least M such that n is a sum of
  consecutive positive integers with largest part M (O. E. Pol, 2025).

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py).
-/
import Mathlib

namespace A212652

/-- Triangular numbers A000217. -/
def T (r : ℕ) : ℕ := r * (r + 1) / 2

lemma two_T (r : ℕ) : 2 * T r = r * (r + 1) := by
  unfold T
  have := Nat.even_mul_succ_self r
  rcases this with ⟨m, hm⟩
  omega

lemma T_mono {a b : ℕ} (h : a ≤ b) : T a ≤ T b := by
  have h1 := two_T a
  have h2 := two_T b
  have : a * (a + 1) ≤ b * (b + 1) := Nat.mul_le_mul h (by omega)
  omega

/-- The defining property: n = T M - T k with 0 ≤ k ≤ M. -/
def Rep (n M : ℕ) : Prop := 1 ≤ M ∧ ∃ k, k ≤ M ∧ n = T M - T k

lemma rep_self (n : ℕ) (hn : 1 ≤ n) : Rep n n := by
  refine ⟨hn, n - 1, by omega, ?_⟩
  have h1 := two_T n
  have h2 := two_T (n - 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2 ⊢
  have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
  omega

lemma exists_rep (n : ℕ) : ∃ M, Rep n M ∨ n = 0 := by
  by_cases hn : 1 ≤ n
  · exact ⟨n, Or.inl (rep_self n hn)⟩
  · exact ⟨0, Or.inr (by omega)⟩

open Classical in
/-- A212652 (for n ≥ 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.find (exists_rep n)

/-- Key identity: 2 (T (k+L) - T k) = L (2k + L + 1). -/
lemma two_diff (k L : ℕ) : 2 * (T (k + L) - T k) = L * (2 * k + L + 1) := by
  have h1 := two_T (k + L)
  have h2 := two_T k
  have hle := T_mono (Nat.le_add_right k L)
  have : (k + L) * (k + L + 1) = k * (k + 1) + L * (2 * k + L + 1) := by ring
  omega

/-- Every representation comes from an odd divisor. -/
lemma rep_to_div {n M : ℕ} (h : Rep n M) :
    ∃ h, h ∣ n ∧ Odd h ∧ M = n / h + (h - 1) / 2 := by
  obtain ⟨_, k, hk, hnk⟩ := h
  obtain ⟨L, rfl⟩ : ∃ L, M = k + L := ⟨M - k, by omega⟩
  have e := two_diff k L
  rw [← hnk] at e
  rcases Nat.even_or_odd L with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- L = 2j even: h = 2k + L + 1 is odd, d = j
    refine ⟨2 * k + L + 1, ⟨j, ?_⟩, ⟨k + j, by omega⟩, ?_⟩
    · subst hj; nlinarith
    · have hn' : n = j * (2 * k + L + 1) := by subst hj; nlinarith
      rw [hn', Nat.mul_div_cancel _ (by omega)]
      omega
  · -- L = 2j+1 odd: h = L, d = k + j + 1
    refine ⟨L, ⟨k + j + 1, ?_⟩, ⟨j, hj⟩, ?_⟩
    · subst hj; nlinarith
    · have hn' : n = L * (k + j + 1) := by subst hj; nlinarith
      rw [hn', Nat.mul_div_cancel_left _ (by omega)]
      omega

/-- Every odd divisor gives a representation. -/
lemma div_to_rep {n h : ℕ} (hn : 1 ≤ n) (hd : h ∣ n) (ho : Odd h) :
    Rep n (n / h + (h - 1) / 2) := by
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨j, rfl⟩ := ho
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; simp at hn
    · exact h0
  rw [Nat.mul_div_cancel_left _ (by omega)]
  have hj : (2 * j + 1 - 1) / 2 = j := by omega
  rw [hj]
  refine ⟨by omega, ?_⟩
  by_cases hc : j + 1 ≤ d
  · -- h ≤ 2d: k = d - j - 1, L = 2j + 1
    refine ⟨d - j - 1, by omega, ?_⟩
    have e := two_diff (d - j - 1) (2 * j + 1)
    have : d - j - 1 + (2 * j + 1) = d + j := by omega
    rw [this] at e
    have : (2 * j + 1) * (2 * (d - j - 1) + (2 * j + 1) + 1) = 2 * ((2 * j + 1) * d) := by
      have : 2 * (d - j - 1) + (2 * j + 1) + 1 = 2 * d := by omega
      rw [this]; ring
    omega
  · -- h > 2d: k = j - d, L = 2d
    refine ⟨j - d, by omega, ?_⟩
    have e := two_diff (j - d) (2 * d)
    have : j - d + 2 * d = d + j := by omega
    rw [this] at e
    have : 2 * d * (2 * (j - d) + 2 * d + 1) = 2 * ((2 * j + 1) * d) := by
      have : 2 * (j - d) + 2 * d + 1 = 2 * j + 1 := by omega
      rw [this]; ring
    omega

lemma a_spec {n : ℕ} (hn : 1 ≤ n) : Rep n (a n) := by
  classical
  have := Nat.find_spec (exists_rep n)
  unfold a
  rcases this with h | h
  · convert h
  · omega

lemma a_min {n M : ℕ} (hM : Rep n M) : a n ≤ M := by
  classical
  unfold a
  exact Nat.find_min' _ (Or.inl hM)

/-- Main theorem: a(n) = min over odd h ∣ n of n/h + (h-1)/2. -/
theorem A212652_formula (n : ℕ) (hn : 1 ≤ n) :
    (∀ h, h ∣ n → Odd h → a n ≤ n / h + (h - 1) / 2) ∧
    (∃ h, h ∣ n ∧ Odd h ∧ a n = n / h + (h - 1) / 2) :=
  ⟨fun _ hd ho => a_min (div_to_rep hn hd ho), rep_to_div (a_spec hn)⟩

/-- Row r of A141419: T(r) - T(r-k), 1 ≤ k ≤ r. -/
def row141419 (r : ℕ) : Set ℕ := {x | ∃ k, 1 ≤ k ∧ k ≤ r ∧ x = T r - T (r - k)}

/-- Row r of A209260: entries of row r of A141419 absent from earlier rows. -/
def row209260 (r : ℕ) : Set ℕ := {x | x ∈ row141419 r ∧ ∀ m < r, x ∉ row141419 m}

lemma mem_row141419_iff_rep {n M : ℕ} (hn : 1 ≤ n) : n ∈ row141419 M ↔ Rep n M := by
  constructor
  · rintro ⟨k, hk1, hkM, rfl⟩
    exact ⟨by omega, M - k, by omega, rfl⟩
  · rintro ⟨hM, k, hk, rfl⟩
    by_cases hkM : k = M
    · subst hkM; simp at hn
    · exact ⟨M - k, by omega, by omega, by rw [Nat.sub_sub_self hk]⟩

/-- n lies in row M of A141419 iff M = n/h + (h-1)/2 for an odd divisor h. -/
theorem mem_row141419_iff (n M : ℕ) (hn : 1 ≤ n) :
    n ∈ row141419 M ↔ ∃ h, h ∣ n ∧ Odd h ∧ M = n / h + (h - 1) / 2 := by
  rw [mem_row141419_iff_rep hn]
  constructor
  · exact rep_to_div
  · rintro ⟨h, hd, ho, rfl⟩
    exact div_to_rep hn hd ho

/-- n appears in row a(n) of A209260, and in no other row. -/
theorem A212652_row209260 (n : ℕ) (hn : 1 ≤ n) :
    n ∈ row209260 (a n) ∧ ∀ r, n ∈ row209260 r → r = a n := by
  refine ⟨⟨(mem_row141419_iff_rep hn).2 (a_spec hn), fun m hm hmem => ?_⟩, ?_⟩
  · have := a_min ((mem_row141419_iff_rep hn).1 hmem)
    omega
  · rintro r ⟨hr, hlt⟩
    have h1 := a_min ((mem_row141419_iff_rep hn).1 hr)
    by_contra hne
    exact hlt (a n) (by omega) ((mem_row141419_iff_rep hn).2 (a_spec hn))

lemma sum_Ioc (k M : ℕ) (h : k ≤ M) : ∑ i ∈ Finset.Ioc k M, i = T M - T k := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hkM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have h1 := two_T (M + 1)
    have h2 := two_T M
    have h3 := T_mono hkM
    have : (M + 1) * (M + 1 + 1) = M * (M + 1) + 2 * (M + 1) := by ring
    omega

/-- Pol's reading: n = (k+1) + ... + M with 0 ≤ k < M, and a(n) is the least such M. -/
def ConsecRep (n M : ℕ) : Prop := ∃ k, k < M ∧ n = ∑ i ∈ Finset.Ioc k M, i

lemma consec_iff (n M : ℕ) (hn : 1 ≤ n) : ConsecRep n M ↔ Rep n M := by
  constructor
  · rintro ⟨k, hk, hs⟩
    exact ⟨by omega, k, hk.le, by rw [hs, sum_Ioc k M hk.le]⟩
  · rintro ⟨hM, k, hk, hs⟩
    rcases Nat.lt_or_ge k M with hlt | hge
    · exact ⟨k, hlt, by rw [hs, sum_Ioc k M hk]⟩
    · have : k = M := by omega
      subst this; simp at hs; omega

theorem A212652_consecutive (n : ℕ) (hn : 1 ≤ n) :
    ConsecRep n (a n) ∧ ∀ M, ConsecRep n M → a n ≤ M :=
  ⟨(consec_iff n _ hn).2 (a_spec hn), fun M hM => a_min ((consec_iff n M hn).1 hM)⟩

