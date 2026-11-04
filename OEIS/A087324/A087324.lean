/-
OEIS A087324 (n such that n and its 9's complement 10^d - 1 - n, d = number of
digits of n, have the same prime signature).  Conjecture (2): every prime
signature occurs.  False: no term has an all-even signature (p^2, p^2 q^2, ...).

A number has an all-even signature iff it is a perfect square.  Equal
signatures would make both n and its complement squares, but they sum to
10^d - 1 ≡ 3 (mod 4) for d ≥ 2, and a sum of two squares is never 3 mod 4.
For d = 1 the pairs (n, 9 - n) are checked directly.

Checked here (core Lean):
* `sq_mod4`: x^2 mod 4 ∈ {0, 1}.
* `main`: for d ≥ 2, x^2 + y^2 ≠ 10^d - 1.
* `one_digit`: for 1 ≤ n ≤ 8, n and 9 - n are not both squares.
Not checked here: "same signature with all exponents even ⇒ both squares"
(definition of prime signature).  Conjecture (1) (infinitely many terms) is
not addressed.
-/

theorem sq_mod4 (x : Nat) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h : x % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize x % 4 = r at h
  match r, h with
  | 0, _ => decide | 1, _ => decide | 2, _ => decide | 3, _ => decide

theorem pow10_mod4 (d : Nat) (hd : 2 ≤ d) : 10 ^ d % 4 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  induction k with
  | zero => decide
  | succ k ih => rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.pow_succ]; omega

theorem main (d x y : Nat) (hd : 2 ≤ d) : x ^ 2 + y ^ 2 ≠ 10 ^ d - 1 := by
  have h1 := sq_mod4 x
  have h2 := sq_mod4 y
  have h3 := pow10_mod4 d hd
  have h4 : 1 ≤ 10 ^ d := Nat.pow_pos (by decide)
  omega

theorem one_digit : (List.range 9).all (fun n => n == 0 ||
    !((List.range 4).any (fun a => a * a == n) && (List.range 4).any (fun b => b * b == 9 - n))) = true := by
  decide
