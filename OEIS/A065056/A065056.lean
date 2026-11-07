/-
OEIS A065056: partial sums of Recaman's sequence A005132.
Conjecture (entry): there is a constant c = 1.9... such that a(n)/n^c is bounded.

False for every c < 2: `A065056_lower` proves 4 * a(n) >= n * (n + 1) for all n,
so a(n)/n^c >= (n^(2-c))/4 is unbounded when c < 2.

Definitions (A005132): R(0) = 0; R(n) = R(n-1) - n if that is >= 0 and not already
in the sequence, otherwise R(n-1) + n. `st n = (R(n), [R(n), ..., R(0)])`.
A065056(n) = R(0) + ... + R(n) (`A065056`, with A065056(0..4) = 0,1,4,10,12 checked
by `decide`).
Checked here: the definitions, the first terms, and the lower bound for all n.
Not checked here: the real-number step from the bound to unboundedness of
a(n)/n^c (immediate), and nothing about c >= 2.
-/

def st : Nat → Nat × List Nat
  | 0 => (0, [0])
  | n + 1 =>
    let a := (st n).1
    let seen := (st n).2
    if n + 1 ≤ a ∧ (a - (n + 1)) ∉ seen then (a - (n + 1), (a - (n + 1)) :: seen)
    else (a + (n + 1), (a + (n + 1)) :: seen)

/-- Recaman's sequence A005132. -/
def R (n : Nat) : Nat := (st n).1

/-- A065056(n) = R(0) + ... + R(n). -/
def A065056 : Nat → Nat
  | 0 => R 0
  | n + 1 => A065056 n + R (n + 1)

theorem R_first : (List.range 10).map R = [0, 1, 3, 6, 2, 7, 13, 20, 12, 21] := by decide

theorem A065056_first : (List.range 10).map A065056 = [0, 1, 4, 10, 12, 19, 32, 52, 64, 85] := by
  decide

/-- Consecutive terms sum to at least the step size. -/
theorem R_pair (n : Nat) : n + 1 ≤ R n + R (n + 1) := by
  unfold R
  show n + 1 ≤ (st n).1 + (st (n + 1)).1
  simp only [st]
  split
  · rename_i h; omega
  · omega

theorem A065056_inv (n : Nat) : n * (n + 1) + 2 * R n ≤ 4 * A065056 n := by
  induction n with
  | zero => simp [A065056, R, st]
  | succ n ih =>
    have hp := R_pair n
    simp only [A065056]
    have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
      rw [Nat.add_mul n 1, Nat.one_mul, Nat.mul_add n (n + 1) 1, Nat.mul_one]; omega
    omega

theorem A065056_lower (n : Nat) : n * (n + 1) ≤ 4 * A065056 n := by
  have := A065056_inv n
  omega
