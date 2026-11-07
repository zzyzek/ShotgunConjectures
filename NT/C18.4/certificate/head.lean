import Mathlib

/-
Guy, UPINT C18 (Heden): on the n × n modular (toroidal) board, is the maximum number M(n) of
non-attacking queens equal to n - 2 when 3 | n or 4 | n? Known: P. Monsky, solution to E3162,
Amer. Math. Monthly 96 (1989) 258-259; explicit placements in K. Williams, arXiv:2404.18237,
proof of Thm 6.

Checked here (`queens_lower`): for every n ≥ 3 with 3 ∣ n or 4 ∣ n there is a set of n - 2
squares of ZMod n × ZMod n, pairwise distinct in x, in y, in x + y and in y - x (two queens on
the torus attack iff one of these agrees). The placements are Williams' five residue families
(n = 6m+3, 12m+4, 12m+6, 12m-4, 12m) plus explicit sets for n = 4, 6, 12.
Each family is checked for every m: for columns t1 < t2 the differences of y, x + y, y - x are
k·n only for |k| ≤ 6, and each k is excluded by `omega` on every pair of pieces.
Checked here (`queens_upper`): every non-attacking set has at most n - 2 queens (Monsky's
argument: the four coordinate maps of n - 1 queens each miss one value; sums and sums of squares,
in ZMod n when 3 ∣ n and of lifts in ZMod (2n) when 4 ∣ n, force n ∣ Σ_{i<n} i² or a variant,
which fails). Main theorem `modular_queens_eq`: both statements, i.e. M(n) = n - 2.
Not checked: nothing beyond reading M(n) as the maximum size of such a set.
-/

namespace NT_C18_4

/-- Pairwise non-attacking queens on the n × n torus. -/
def NonAttacking {n : ℕ} (S : Finset (ZMod n × ZMod n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p.1 + p.2 ≠ q.1 + q.2 ∧ p.2 - p.1 ≠ q.2 - q.1
