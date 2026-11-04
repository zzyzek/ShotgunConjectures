/-
OEIS A115038 (smallest x with x^2 + prime(n) a perfect power).  Conjecture:
for every prime p there are x, y, k (k ≥ 2) with x^2 + p = y^k.  True (trivial).

Checked here (core Lean, full statement):
* `odd_case`: for odd p ≥ 3, ((p-1)/2)^2 + p = ((p+1)/2)^2 with (p+1)/2 ≥ 2.
* `two_case`: 5^2 + 2 = 3^3.
Not checked here: nothing (every prime is 2 or odd).
-/

theorem odd_case (p : Nat) (hp : p % 2 = 1) (h3 : 3 ≤ p) :
    (p / 2) ^ 2 + p = (p / 2 + 1) ^ 2 ∧ 2 ≤ p / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  have hk : (2 * k + 1) / 2 = k := by omega
  rw [hk]
  refine ⟨?_, by omega⟩
  grind

theorem two_case : 5 ^ 2 + 2 = 3 ^ 3 := by decide
