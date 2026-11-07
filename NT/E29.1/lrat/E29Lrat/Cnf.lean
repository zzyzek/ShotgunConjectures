import OpenProblemsLib.LRAT

/-!
# NT-E29.1: the CNF for colourings of [3, N], defined from the problem

`Forces N`: every 2-colouring of the integers has `x < y` with `x ≥ 3`, `x y ≤ N` and
`x, y, x + y, x y` all of one colour (only the colours on `[3, N]` matter, because
`3 ≤ x < y < x + y ≤ x y ≤ N`).

`cnf N` has one variable per integer (literal codes `2 n` for "n has colour true", `2 n + 1`
for "n has colour false", see `OpenProblemsLib.LRAT.litT`) and, for every `x ≥ 3`, `x < y`,
`x y ≤ N`, the two clauses "not all false" and "not all true" on `x, y, x + y, x y`, in the
order of `certificate/certify.py` (x ascending, then y ascending, positive clause first).

Checked: `sat_of_free` (a colouring without a monochromatic quadruple satisfies `cnf N`) and
`forces_of_unsat` (so `Unsat (cnf N)` gives `Forces N`). Axioms propext, Classical.choice,
Quot.sound at most.
-/

namespace E29Lrat

open OpenProblemsLib.LRAT

/-- `x, y, x + y, x y` all have the same colour under `c`. -/
def Mono (c : Nat → Bool) (x y : Nat) : Prop :=
  c x = c y ∧ c y = c (x + y) ∧ c (x + y) = c (x * y)

/-- Every 2-colouring has a monochromatic `x, y, x + y, x y` with `3 ≤ x < y`, `x y ≤ N`. -/
def Forces (N : Nat) : Prop := ∀ c : Nat → Bool, ∃ x y, 3 ≤ x ∧ x < y ∧ x * y ≤ N ∧ Mono c x y

/-- "Not all false" on `x, y, x + y, x y`. -/
def posC (x y : Nat) : List Nat := [2 * x, 2 * y, 2 * (x + y), 2 * (x * y)]

/-- "Not all true" on `x, y, x + y, x y`. -/
def negC (x y : Nat) : List Nat := [2 * x + 1, 2 * y + 1, 2 * (x + y) + 1, 2 * (x * y) + 1]

/-- Row `x`: `y = x + 1, ..., N / x`, both clauses for each `y`. -/
def row (N x : Nat) : List (List Nat) :=
  (List.range (N / x - x)).flatMap fun i => [posC x (x + 1 + i), negC x (x + 1 + i)]

/-- All rows `x = 3, ..., N`. -/
def cnf (N : Nat) : List (List Nat) := (List.range (N - 2)).flatMap fun i => row N (3 + i)

theorem litT_two (c : Nat → Bool) (n : Nat) : litT c (2 * n) = c n := by
  unfold litT
  rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]
  cases c n <;> rfl

theorem litT_two_one (c : Nat → Bool) (n : Nat) : litT c (2 * n + 1) = !c n := by
  unfold litT
  rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
  cases c n <;> rfl

theorem mem_cnf {N : Nat} {cl : List Nat} (h : cl ∈ cnf N) :
    ∃ x y, 3 ≤ x ∧ x < y ∧ x * y ≤ N ∧ (cl = posC x y ∨ cl = negC x y) := by
  simp only [cnf, row, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨i, _, j, hj, hcl⟩ := h
  refine ⟨3 + i, 3 + i + 1 + j, by omega, by omega, ?_, hcl⟩
  have hy : 3 + i + 1 + j ≤ N / (3 + i) := by omega
  have := (Nat.le_div_iff_mul_le (by omega)).mp hy
  rw [Nat.mul_comm]; exact this

/-- A colouring with no monochromatic quadruple satisfies `cnf N`. -/
theorem sat_of_free (N : Nat) (c : Nat → Bool)
    (h : ∀ x y, 3 ≤ x → x < y → x * y ≤ N → ¬ Mono c x y) : Satisfies c (cnf N) := by
  intro cl hcl
  obtain ⟨x, y, h1, h2, h3, hc⟩ := mem_cnf hcl
  have hm := h x y h1 h2 h3
  unfold Mono at hm
  rcases hc with rfl | rfl
  · simp only [csat, posC, List.any_cons, List.any_nil, litT_two, Bool.or_false]
    cases hx : c x <;> cases hy : c y <;> cases hs : c (x + y) <;> cases hp : c (x * y) <;>
      simp_all
  · simp only [csat, negC, List.any_cons, List.any_nil, litT_two_one, Bool.or_false]
    cases hx : c x <;> cases hy : c y <;> cases hs : c (x + y) <;> cases hp : c (x * y) <;>
      simp_all

/-- Unsatisfiability of `cnf N` gives `Forces N`. -/
theorem forces_of_unsat (N : Nat) (hu : Unsat (cnf N)) : Forces N := by
  intro c
  apply Classical.byContradiction
  intro hne
  apply hu c
  apply sat_of_free
  intro x y h1 h2 h3 hm
  exact hne ⟨x, y, h1, h2, h3, hm⟩

end E29Lrat
