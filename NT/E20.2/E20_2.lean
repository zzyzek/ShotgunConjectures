/-
Guy, Unsolved Problems in Number Theory (3rd ed.), E20: N_d(n) is the greatest length
of a sequence on n letters with no two equal adjacent terms and no alternating
subsequence a b a b ... (a != b) of length d + 1. Known: N_5(n) = 1, 5, 10, 16, 22, 29
for n <= 6 (OEIS A005280). New: N_5(7) = 37.

Checked here (core Lean, kernel `decide`): the 37-term sequence `w` below uses only the
letters 1..7, has no two equal adjacent terms, and for every pair of letters a < b
its restriction to {a, b} has at most 5 maximal blocks (so no alternation of length 6).
Hence N_5(7) >= 37 (`E20_2_main`).
Not checked here: N_5(7) <= 37, which rests on the exhaustive memoised search
certificate/ds.cpp (25 613 680 states), outside Lean.
-/

def w : List Nat := [1, 2, 3, 2, 4, 2, 5, 2, 6, 2, 6, 5, 6, 4, 6, 3, 6, 7, 6, 7, 3, 7, 4, 7, 5, 7, 1, 7, 1, 5, 1, 4, 1, 3, 1, 2, 1]

/-- number of maximal blocks of equal terms in a list. -/
def blocks : List Nat → Nat
  | [] => 0
  | [_] => 1
  | x :: y :: t => (if x = y then 0 else 1) + blocks (y :: t)

/-- longest alternation between letters a and b in s: blocks of the restriction. -/
def alt (s : List Nat) (a b : Nat) : Nat := blocks (s.filter (fun x => x == a || x == b))

def noAdjRep : List Nat → Bool
  | x :: y :: t => (x != y) && noAdjRep (y :: t)
  | _ => true

theorem w_length : w.length = 37 := by decide
theorem w_letters : ∀ x ∈ w, 1 ≤ x ∧ x ≤ 7 := by decide
theorem w_noAdj : noAdjRep w = true := by decide
theorem w_alt : ∀ a : Fin 8, ∀ b : Fin 8, a.val < b.val → alt w a.val b.val ≤ 5 := by decide

/-- Main: a Davenport–Schinzel sequence of degree 5 on 7 letters of length 37,
so N_5(7) >= 37. -/
theorem E20_2_main : ∃ s : List Nat, s.length = 37 ∧ (∀ x ∈ s, 1 ≤ x ∧ x ≤ 7) ∧
    noAdjRep s = true ∧ (∀ a b : Nat, a < b → b ≤ 7 → alt s a b ≤ 5) :=
  ⟨w, w_length, w_letters, w_noAdj, fun a b hab hb =>
    w_alt ⟨a, by omega⟩ ⟨b, by omega⟩ hab⟩
