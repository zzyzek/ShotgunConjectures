import Mathlib

/-
OEIS-A023402 (Mathlib). Conjectures (OEIS wiki Talk:Conjectures/List): A023402(n) = T(n+2, 3),
the 3rd smallest divisor of the smallest number with exactly n+2 divisors (A081532 notation),
and A081532: T(n, 3) = A023402(n-2) for n > 2. README result: both false, A023402(2) = 4 but
T(4, 3) = 3.

Reading of A023402 formalised here: A023402(k) is the k-th last decimal digit of any power
2^e whose last k digits are all 3 or 4 (the README's reading). For k = 2 this digit is
determined: `A023402_two` shows that some 2^e has its last two digits in {3, 4}
(2^18 = 262144) and that every such 2^e has last two digits 44, so A023402(2) = 4 (and
A023402(1) = 4).

Main theorem `A023402_main`: A023402_two together with: 6 is the least natural number with
exactly 4 divisors (Mathlib `IsLeast`, `Nat.divisors`), its divisors are {1, 2, 3, 6}, and 3 is
a divisor with exactly two smaller divisors, so T(4, 3) = 3 ≠ 4 = A023402(2).

Outside Lean: only the reading of the A023402 definition stated above.
-/

/-- The last two decimal digits of `x` are both 3 or 4. -/
def lastTwo34 (x : ℕ) : Prop :=
  (x % 10 = 3 ∨ x % 10 = 4) ∧ (x / 10 % 10 = 3 ∨ x / 10 % 10 = 4)

theorem A023402_two :
    (∃ e, lastTwo34 (2 ^ e)) ∧ ∀ e, lastTwo34 (2 ^ e) → 2 ^ e % 10 = 4 ∧ 2 ^ e / 10 % 10 = 4 := by
  refine ⟨⟨18, by unfold lastTwo34; norm_num⟩, ?_⟩
  intro e h
  unfold lastTwo34 at h
  rcases e with _ | _ | e
  · norm_num at h
  · norm_num at h
  · have h4 : 2 ^ (e + 2) % 4 = 0 := by
      rw [pow_add]; simp [Nat.mul_mod_left]
    omega

theorem least_four : IsLeast {m : ℕ | m.divisors.card = 4} 6 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hm' : m.divisors.card = 4 := hm
  by_contra h
  interval_cases m <;> revert hm' <;> decide

theorem divisors_six : Nat.divisors 6 = {1, 2, 3, 6} := by
  decide

theorem A023402_main :
    ((∃ e, lastTwo34 (2 ^ e)) ∧ ∀ e, lastTwo34 (2 ^ e) → 2 ^ e % 10 = 4 ∧ 2 ^ e / 10 % 10 = 4) ∧
      IsLeast {m : ℕ | m.divisors.card = 4} 6 ∧ Nat.divisors 6 = {1, 2, 3, 6} ∧
      (3 ∈ Nat.divisors 6 ∧ ((Nat.divisors 6).filter (· < 3)).card = 2) :=
  ⟨A023402_two, least_four, divisors_six, by rw [divisors_six]; decide⟩
