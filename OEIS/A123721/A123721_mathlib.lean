import Mathlib

/-
OEIS A123721: a(n) = A123249(n) - 2n, where A123249(1) = 1 and A123249(n) = n + (smallest
integer >= n missing from A123249(1..n-1)).
Conjecture (entry): for k > 1 the smallest n with a(n) = k is A123720(k) = 2^k + 2^(k-1) - k.

Definitions (namespace OEIS_A123721).
* `A123249`: the entry's definition, via `mexAbove f n` = least x >= n with x not among
  f 1, ..., f (n-1) (Nat.find).
* `A123721 n = A123249 n - 2 n` (in ℤ; the data's a(1) = 1 is A123249(1) itself; n = 1
  is irrelevant for k >= 1 under either reading).
* `G k = 3·2^k - k - 1` (= A123720(k+1), `G_eq_A123720`).

Main theorems.
* `A123721_first k : A123721 (G k) = k ∧ ∀ n, 1 ≤ n → n < G k → A123721 n ≠ k`
  (the corrected statement: the first k occurs at A123720(k+1)).
* `A123721_misstated`: a(4) = 1, a(9) = 2 and a(n) ≠ 2 for n < 9, so the stated
  A123720(2) = 4 is wrong (index shifted by one).
Route: `Spec` (the defining properties), `spec` (A123249 satisfies them); with d(n) = mex - n,
a(n) = 2n + d(n) (`a_eq`); `run` (d(n) >= K+1 makes n..n+K consecutive terms, hence a
descending staircase of d), `stair`, `up` (d(j) = k gives d(2j + k) >= k + 1), and `main`
(induction: G(k+1) = 2 G(k) + k is the first n with d(n) >= k + 1, and d there is k + 1).
Not checked here: agreement with the OEIS data (certificate/check.py).
-/

namespace OEIS_A123721

/-! ## abstract part: any a, m with the defining properties -/

structure Spec (a m : ℕ → ℕ) : Prop where
  a1 : a 1 = 1
  h1 : ∀ n, 2 ≤ n → n ≤ m n
  h2 : ∀ n, 2 ≤ n → ∀ i, 1 ≤ i → i < n → a i ≠ m n
  h3 : ∀ n, 2 ≤ n → ∀ x, n ≤ x → x < m n → ∃ i, 1 ≤ i ∧ i < n ∧ a i = x
  h4 : ∀ n, 2 ≤ n → a n = n + m n

variable {a m : ℕ → ℕ}

theorem m_mono (S : Spec a m) (i : ℕ) (hi : 2 ≤ i) : m i ≤ m (i + 1) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj1, hji, hj⟩ := S.h3 i hi (m (i + 1)) (by have := S.h1 (i + 1) (by omega); omega) h
  exact S.h2 (i + 1) (by omega) j hj1 (by omega) hj

theorem a_succ (S : Spec a m) (i : ℕ) (hi : 1 ≤ i) : a i < a (i + 1) := by
  rcases Nat.lt_or_ge i 2 with h | h
  · obtain rfl : i = 1 := by omega
    rw [S.a1, S.h4 2 le_rfl]; have := S.h1 2 le_rfl; omega
  · rw [S.h4 i h, S.h4 (i + 1) (by omega)]; have := m_mono S i h; omega

theorem a_lt (S : Spec a m) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : a i < a j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h | h
    · exact (ih h).trans (a_succ S j (by omega))
    · obtain rfl : i = j := by omega
      exact a_succ S i hi

theorem a_le (S : Spec a m) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : a i ≤ a j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (a_lt S hi h).le

/-- d n = m n - n, so a n = 2 n + d n. -/
def d (m : ℕ → ℕ) (n : ℕ) : ℕ := m n - n

theorem a_eq (S : Spec a m) (n : ℕ) (hn : 2 ≤ n) : a n = 2 * n + d m n := by
  rw [S.h4 n hn, d]; have := S.h1 n hn; omega

theorem a_ge (S : Spec a m) (n : ℕ) (hn : 1 ≤ n) : n ≤ a n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [S.a1]
  · rw [a_eq S n h]; omega

/-- Run lemma: if d n ≥ K + 1 then n, ..., n + K are consecutive terms a(i), ..., a(i+K). -/
theorem run (S : Spec a m) (n K : ℕ) (hn : 2 ≤ n) (hd : K + 1 ≤ d m n) :
    ∃ i, 2 ≤ i ∧ i < n ∧ ∀ t ≤ K, a (i + t) = n + t := by
  have hlt : ∀ x, n ≤ x → x ≤ n + K → x < m n := by
    intro x h1 h2; unfold d at hd; omega
  obtain ⟨i, hi1, hin, hai⟩ := S.h3 n hn n le_rfl (hlt n le_rfl (by omega))
  have hi2 : 2 ≤ i := by
    by_contra h
    obtain rfl : i = 1 := by omega
    rw [S.a1] at hai; omega
  refine ⟨i, hi2, hin, ?_⟩
  intro t ht
  induction t with
  | zero => simpa using hai
  | succ t ih =>
    have ih := ih (by omega)
    obtain ⟨j, hj1, hjn, haj⟩ := S.h3 n hn (n + (t + 1)) (by omega) (hlt _ (by omega) (by omega))
    have hij : i + t < j := by
      by_contra h
      have := a_le S hj1 (show j ≤ i + t by omega)
      omega
    have h1 := a_le S (by omega) (show i + (t + 1) ≤ j by omega)
    have h2 := a_succ S (i + t) (by omega)
    rw [show i + t + 1 = i + (t + 1) by ring] at h2
    omega

/-- Forward staircase: if d j = k then a (j + t) = 2 j + k + t for t ≤ k. -/
theorem stair (S : Spec a m) (j k : ℕ) (hj : 2 ≤ j) (hd : d m j = k) :
    ∀ t ≤ k, a (j + t) = 2 * j + k + t := by
  intro t ht
  have hmj : m j = j + k := by unfold d at hd; have := S.h1 j hj; omega
  have hm : m (j + t) = j + k := by
    apply le_antisymm
    · by_contra h
      push Not at h
      obtain ⟨i, hi1, hit, hai⟩ := S.h3 (j + t) (by omega) (j + k) (by omega) h
      rcases Nat.lt_or_ge i j with hij | hij
      · exact S.h2 j hj i hi1 hij (by rw [hai, hmj])
      · have := a_le S (by omega) hij
        rw [a_eq S j hj, hd] at this
        omega
    · have : m j ≤ m (j + t) := by
        induction t with
        | zero => simp
        | succ t ih => exact (ih (by omega)).trans (by rw [← add_assoc]; exact m_mono S _ (by omega))
      omega
  rw [S.h4 _ (by omega), hm]; omega

/-- d (2 j + k) ≥ k + 1 when d j = k. -/
theorem up (S : Spec a m) (j k : ℕ) (hj : 2 ≤ j) (hd : d m j = k) : k + 1 ≤ d m (2 * j + k) := by
  have hs := stair S j k hj hd
  have hn : 2 ≤ 2 * j + k := by omega
  have : 2 * j + k + k + 1 ≤ m (2 * j + k) := by
    by_contra h
    push Not at h
    have hge := S.h1 _ hn
    set x := m (2 * j + k)
    have hx := S.h2 _ hn (j + (x - (2 * j + k))) (by omega) (by omega)
    apply hx
    rw [hs _ (by omega)]; omega
  unfold d; omega

/-- G k = 3·2^k - k - 1. -/
def G (k : ℕ) : ℕ := 3 * 2 ^ k - k - 1

theorem G_succ (k : ℕ) : G (k + 1) = 2 * G k + k := by
  have : k + 1 < 3 * 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k); omega
  unfold G; rw [pow_succ]; omega

theorem G_ge (k : ℕ) : 2 ≤ G k := by
  have := Nat.lt_two_pow_self (n := k); unfold G; omega

theorem main (S : Spec a m) : ∀ k, d m (G k) = k ∧ ∀ n, 2 ≤ n → n < G k → d m n < k := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, fun n h1 h2 => by simp [G] at h2; omega⟩
    show d m 2 = 0
    have h := S.h1 2 le_rfl
    unfold d
    by_contra hc
    obtain ⟨i, hi1, hi2, hai⟩ := S.h3 2 le_rfl 2 le_rfl (by omega)
    obtain rfl : i = 1 := by omega
    rw [S.a1] at hai; omega
  | succ k ih =>
    obtain ⟨hdk, hbelow⟩ := ih
    set j := G k
    have hj := G_ge k
    have hup := up S j k hj hdk
    rw [G_succ]
    -- no n < 2 j + k has d n ≥ k + 1
    have hlow : ∀ n, 2 ≤ n → n < 2 * j + k → d m n < k + 1 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
        intro hn2 hnlt
        by_contra hc
        push Not at hc
        obtain ⟨i, hi2, hin, hrun⟩ := run S n k hn2 hc
        have hdi : d m i = d m (i + k) + k := by
          have e1 := hrun 0 (by omega)
          have e2 := hrun k le_rfl
          rw [add_zero, a_eq S i hi2] at e1
          rw [a_eq S (i + k) (by omega)] at e2
          omega
        have hdi_le : d m i < k + 1 := ihn i hin hi2 (by omega)
        have hdi_eq : d m i = k := by omega
        have hiG : j ≤ i := by
          by_contra h; push Not at h
          have := hbelow i hi2 h; omega
        have e1 := hrun 0 (by omega)
        rw [add_zero, a_eq S i hi2, hdi_eq] at e1
        omega
    refine ⟨?_, hlow⟩
    apply le_antisymm _ hup
    by_contra hc
    push Not at hc
    obtain ⟨i, hi2, hin, hrun⟩ := run S (2 * j + k) (k + 1) (by omega) (by omega)
    have e1 := hrun 0 (by omega)
    have e2 := hrun (k + 1) le_rfl
    rw [add_zero, a_eq S i hi2] at e1
    rw [a_eq S (i + (k + 1)) (by omega)] at e2
    have := hlow i hi2 hin
    omega

/-! ## the OEIS sequences -/

theorem exists_missing (f : ℕ → ℕ) (n : ℕ) : ∃ x, n ≤ x ∧ ∀ i, 1 ≤ i → i < n → f i ≠ x := by
  refine ⟨n + ∑ i ∈ Finset.range n, f i + 1, by omega, fun i _ hi h => ?_⟩
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_range.mpr hi)
  omega

open Classical in
/-- Smallest integer ≥ n that is not among f 1, ..., f (n-1). -/
noncomputable def mexAbove (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.find (exists_missing f n)

/-- A123249: a(1) = 1; a(n) = n + (smallest integer ≥ n missing from a(1..n-1)). -/
noncomputable def A123249 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2) + mexAbove (fun i => if _h : i < n + 2 then A123249 i else 0) (n + 2)

/-- A123721(n) = A123249(n) - 2n. -/
noncomputable def A123721 (n : ℕ) : ℤ := (A123249 n : ℤ) - 2 * n

noncomputable def mm (n : ℕ) : ℕ := mexAbove (fun i => if i < n then A123249 i else 0) n

theorem spec : Spec A123249 mm := by
  classical
  refine ⟨by simp [A123249], ?_, ?_, ?_, ?_⟩
  · intro n _; exact (Nat.find_spec (exists_missing _ n)).1
  · intro n _ i hi1 hin h
    have := (Nat.find_spec (exists_missing (fun i => if i < n then A123249 i else 0) n)).2 i hi1 hin
    simp only [hin, ite_true] at this
    exact this h
  · intro n _ x hnx hx
    have := Nat.find_min (exists_missing (fun i => if i < n then A123249 i else 0) n) hx
    push Not at this
    obtain ⟨i, hi1, hin, hi⟩ := this hnx
    simp only [hin, ite_true] at hi
    exact ⟨i, hi1, hin, hi⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [A123249]
    unfold mm
    congr 2

theorem A123721_eq (n : ℕ) (hn : 2 ≤ n) : A123721 n = (d mm n : ℤ) := by
  unfold A123721; rw [a_eq spec n hn]; push_cast; ring

/-- Corrected conjecture: for every k the smallest n with A123721(n) = k is
3·2^k - k - 1 = A123720(k+1). -/
theorem A123721_first (k : ℕ) :
    A123721 (G k) = k ∧ ∀ n, 1 ≤ n → n < G k → A123721 n ≠ k := by
  obtain ⟨h1, h2⟩ := main spec k
  refine ⟨by rw [A123721_eq _ (G_ge k), h1], fun n hn1 hnG => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [A123721, A123249]
  · rw [A123721_eq n h]
    have := h2 n h hnG
    omega

theorem G_eq_A123720 (k : ℕ) : G k = 2 ^ (k + 1) + 2 ^ k - (k + 1) := by
  unfold G; rw [pow_succ]; omega

/-- The conjecture as stated (smallest n with a(n) = k is 2^k + 2^(k-1) - k) fails at k = 2:
a(4) = 1, and the smallest n with a(n) = 2 is 9. -/
theorem A123721_misstated : A123721 4 = 1 ∧ A123721 9 = 2 ∧ ∀ n, 1 ≤ n → n < 9 → A123721 n ≠ 2 := by
  have h1 := (A123721_first 1).1
  have h2 := A123721_first 2
  simp only [G] at h1 h2
  norm_num at h1 h2
  exact ⟨h1, h2.1, h2.2⟩
