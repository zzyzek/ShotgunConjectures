import Mathlib

/-
OEIS A143132: binomial transform of [1, 5, 15, 35, 70, 0, 0, 0, ...],
a(n) = Sum_{k=0..n} C(n,k) c(k) with c = (1, 5, 15, 35, 70, 0, 0, ...).
Conjecture (entry, 2008): the rightmost digit of the terms cycles 1, 6, 6, 6.

Main theorem.
* `A143132_last_digit`: a n % 10 = if n % 4 = 0 then 1 else 6, for every n.

Route.  `a_eq`: only k <= 4 contributes.  `choose_add40`: by Vandermonde
(`Nat.add_choose_eq`) C(n+40,k) = C(n,k) + (multiples of C(40,j), j = 1..4),
and C(40,j) is divisible by 10 for j = 1..4, so a(n+40) = a(n) mod 10.
The 40 residues n < 40 are checked by `decide`.

Checked: everything above, from the definition `a`.  Not checked: agreement
of `a` with the OEIS data terms (certificate/check.py).
-/

namespace A143132

/-- The sequence (1, 5, 15, 35, 70, 0, 0, ...) whose binomial transform is A143132. -/
def c (k : ℕ) : ℕ := [1, 5, 15, 35, 70].getD k 0

/-- A143132 as defined in the entry: the binomial transform of `c`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * c k

/-- Only the terms k ≤ 4 contribute. -/
def b (n : ℕ) : ℕ :=
  n.choose 0 * 1 + n.choose 1 * 5 + n.choose 2 * 15 + n.choose 3 * 35 + n.choose 4 * 70

lemma c_eq_zero {k : ℕ} (hk : 5 ≤ k) : c k = 0 := by
  unfold c
  rw [List.getD_eq_default]
  simp only [List.length_cons, List.length_nil]
  omega

lemma sum_eq (n : ℕ) : ∀ m, 5 ≤ m →
    ∑ k ∈ Finset.range m, n.choose k * c k = b n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp [Finset.sum_range_succ, b, c]
  | succ m hm ih => rw [Finset.sum_range_succ, ih, c_eq_zero hm, mul_zero, add_zero]

lemma a_eq (n : ℕ) : a n = b n := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> decide
  · exact sum_eq n (n + 1) (by omega)

lemma choose_add40 (n k : ℕ) (hk : k ≤ 4) :
    (n + 40).choose k % 10 = n.choose k % 10 := by
  rw [Nat.add_choose_eq]
  interval_cases k <;>
    simp [Finset.Nat.antidiagonal_succ, Nat.choose] <;> omega

lemma b_add40 (n : ℕ) : b (n + 40) % 10 = b n % 10 := by
  unfold b
  have h0 := choose_add40 n 0 (by norm_num)
  have h1 := choose_add40 n 1 (by norm_num)
  have h2 := choose_add40 n 2 (by norm_num)
  have h3 := choose_add40 n 3 (by norm_num)
  have h4 := choose_add40 n 4 (by norm_num)
  omega

lemma b_small : ∀ n < 40, b n % 10 = if n % 4 = 0 then 1 else 6 := by decide

theorem A143132_last_digit (n : ℕ) : a n % 10 = if n % 4 = 0 then 1 else 6 := by
  rw [a_eq]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 40 with h | h
    · exact b_small n h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 40 := ⟨n - 40, by omega⟩
      rw [b_add40, ih m (by omega)]
      have : (m + 40) % 4 = m % 4 := by omega
      rw [this]

