/-
OEIS A085765 (A085765(n) = A086450(2n)).  Conjecture: a(n) mod 2 repeats the
7-pattern 0,0,1,1,1,0,1.  True; it follows from the A086450 pattern (proved in
the OEIS by L. Herrgesell, 2007), re-derived here as finite tables.

A086450: b(0) = 1, b(2n+1) = b(n), b(2n) = b(0) + ... + b(n) (n ≥ 1).
Claim: b(n) mod 2 = P(n mod 7) with P = 1,1,0,1,0,0,1.  Strong induction:
* odd index: P((2r+1) mod 7) = P(r)   (`odd_step`);
* even index: b(2n) = b(0)+...+b(n); P sums to 4 over a period (`period_even`),
  so the sum mod 2 is Q(n mod 7), Q the prefix sums of P mod 2, and
  P(2r mod 7) = Q(r)   (`even_step`).
Then A085765(n) mod 2 = P(2n mod 7) = 1,0,0,1,1,1,0,... (`bisection`), the
stated pattern 0,0,1,1,1,0,1 read from n = 1.

Checked here (core Lean, `decide`): the four finite table facts.
Not checked here: the strong induction itself (two lines, above), the base
b(0) = 1 ≡ P(0), and that A085765 is the even bisection of A086450.
-/

def P : List Nat := [1, 1, 0, 1, 0, 0, 1]
def Q (r : Nat) : Nat := ((P.take (r + 1)).sum) % 2

theorem odd_step : (List.range 7).all (fun r => P[(2 * r + 1) % 7]! == P[r]!) = true := by decide
theorem period_even : P.sum = 4 := by decide
theorem even_step : (List.range 7).all (fun r => P[(2 * r) % 7]! == Q r) = true := by decide
theorem bisection : (List.range 7).map (fun n => P[(2 * (n + 1)) % 7]!) = [0, 0, 1, 1, 1, 0, 1] := by decide
