/-
OEIS A081532 (and A023402), Mathlib proof.

A081532: triangle read by rows; let m be the smallest number with n
divisors, then row n gives the divisors of m (increasing): T(n, k) is the
k-th smallest divisor of m. A023402: "If any power of 2 ends with k 3's and
4's, they must be the first k terms of this sequence in reverse order."
Conjectures (OEIS wiki Talk:Conjectures/List): T(n, 3) = A023402(n - 2) for
n > 2 (A081532), equivalently A023402(n) = T(n + 2, 3) (A023402).

Definitions here, from the OEIS definitions:
* `A081532_T n k`: the k-th entry (1-based) of the increasing list of
  divisors of the least m with exactly n divisors (`Nat.find`, `Nat.divisors`,
  `Nat.nth` with index k - 1).
* `A081532_IsA023402 a`: the defining property of A023402: for every k and
  e, if the last k decimal digits of 2^e are all 3 or 4, then the i-th last
  digit is a(i) for 1 ≤ i ≤ k.

Main theorem `A081532_main`: T(4, 3) = 3, and every sequence a with the
A023402 property has a(2) = 4 (2^18 = 262144 ends in 44). So
T(4, 3) ≠ A023402(2): both conjectures fail (n = 4, resp. n = 2), the README
result. The reading of A023402 is its OEIS name, formalised above.
Nothing else is outside Lean.
-/
import Mathlib

theorem A081532_exists (n : ℕ) : ∃ m : ℕ, m.divisors.card = n := by
  rcases n with _ | n
  · exact ⟨0, by simp⟩
  · exact ⟨2 ^ n, by rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]⟩

/-- T(n, k): the k-th smallest divisor of the least number with exactly n divisors. -/
noncomputable def A081532_T (n k : ℕ) : ℕ :=
  Nat.nth (· ∈ (Nat.find (A081532_exists n)).divisors) (k - 1)

/-- The i-th last decimal digit of x (i = 1 is the units digit). -/
def A081532_digit (x i : ℕ) : ℕ := x / 10 ^ (i - 1) % 10

/-- The defining property of A023402. -/
def A081532_IsA023402 (a : ℕ → ℕ) : Prop :=
  ∀ k e : ℕ, (∀ i, 1 ≤ i → i ≤ k → A081532_digit (2 ^ e) i = 3 ∨ A081532_digit (2 ^ e) i = 4) →
    ∀ i, 1 ≤ i → i ≤ k → A081532_digit (2 ^ e) i = a i

theorem A081532_find_four : Nat.find (A081532_exists 4) = 6 := by
  rw [Nat.find_eq_iff]
  refine ⟨by decide, fun m hm => ?_⟩
  interval_cases m <;> decide

theorem A081532_main :
    A081532_T 4 3 = 3 ∧
    ∀ a : ℕ → ℕ, A081532_IsA023402 a → a 2 = 4 ∧ A081532_T 4 3 ≠ a 2 := by
  have hT : A081532_T 4 3 = 3 := by
    rw [A081532_T, A081532_find_four]
    have h3 : Nat.count (· ∈ Nat.divisors 6) 3 = 2 := by decide
    rw [show 3 - 1 = 2 from rfl, ← h3]
    exact Nat.nth_count (p := (· ∈ Nat.divisors 6)) (by decide)
  refine ⟨hT, fun a ha => ?_⟩
  have h := ha 2 18 (by
    intro i hi1 hi2
    interval_cases i <;> decide) 2 (by norm_num) le_rfl
  have h2 : a 2 = 4 := by rw [← h]; decide
  exact ⟨h2, by rw [hT, h2]; norm_num⟩
