import Mathlib

/-!
# OEIS A122957: the comment "except for 1,2,3,4, this is the nonzero values of A066362" is false

* A122957: numbers `n` such that `φ m ≥ φ n` for every `m > n` (`InA122957`).
* A066362: `a n` = least `k > n` with `φ k < φ n`, or `0` if there is none (`A066362`).

Checked:
* `A066362_21 : A066362 21 = 22` (so 22 is a nonzero value of A066362) and
  `not_A122957_22 : ¬ InA122957 22` (`φ 24 = 8 < 10 = φ 22`); together `A122957_misstated`.
* `A066362_eq_zero_iff : A066362 n = 0 ↔ InA122957 n` for every `n`: A122957 is the zero set
  of A066362 (this is the cross-reference "zeros of A066362" in the entry; 1, 2, 3, 4 included).
Not checked: nothing beyond reading the two definitions.
-/

namespace A122957

/-- `n` is a term of A122957. -/
def InA122957 (n : ℕ) : Prop := ∀ m, n < m → Nat.totient n ≤ Nat.totient m

open Classical in
/-- A066362. -/
noncomputable def A066362 (n : ℕ) : ℕ :=
  if h : ∃ k, n < k ∧ Nat.totient k < Nat.totient n then Nat.find h else 0

theorem A066362_21 : A066362 21 = 22 := by
  have h : ∃ k, 21 < k ∧ Nat.totient k < Nat.totient 21 := ⟨22, by decide, by decide⟩
  rw [A066362]; simp only [h, ↓reduceDIte]; rw [Nat.find_eq_iff]
  exact ⟨⟨by decide, by decide⟩, fun k hk h' => by omega⟩

theorem not_A122957_22 : ¬ InA122957 22 := by
  intro h
  have := h 24 (by decide)
  revert this; decide

theorem A122957_misstated : (∃ n, A066362 n = 22) ∧ ¬ InA122957 22 :=
  ⟨⟨21, A066362_21⟩, not_A122957_22⟩

theorem A066362_eq_zero_iff (n : ℕ) : A066362 n = 0 ↔ InA122957 n := by
  unfold A066362 InA122957
  by_cases h : ∃ k, n < k ∧ Nat.totient k < Nat.totient n
  · simp only [h, ↓reduceDIte]
    constructor
    · intro h0
      have := Nat.find_spec h
      rw [h0] at this; omega
    · intro hall
      obtain ⟨k, hk, hlt⟩ := h
      have := hall k hk; omega
  · simp only [h, ↓reduceDIte]
    simp only [true_iff]
    intro m hm
    by_contra hc
    exact h ⟨m, hm, by omega⟩
