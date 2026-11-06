# OEIS A228469, A228471: least c with an alternating trace (Kimberling)

**Source.** OEIS [A228469](https://oeis.org/A228469) and [A228471](https://oeis.org/A228471) (Clark Kimberling,
Aug 22 2013), both defined by a(n) = 6a(n-2) + a(n-4) with a(0..3) = 2, 8, 13, 49 and 3, 5, 19, 31.
Conjecture in each: a(n) is the least positive integer c for which there is a positive integer b with trace(b,c)
equal to the first letters of 01010... (A228469), 10101... (A228471). The trace (A228469): from (x,y), with
u(x,y) = (y, x mod y), v(x,y) = (y, y - (x mod y)), apply w = min(u,v) until the second entry is the gcd,
recording 0 when w = u and 1 otherwise. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** min compares pairs with equal first entry, so w = u iff r <= y - r (r = x mod y; ties give 0).
The run stops when y divides x. This gives trace(18,13) = 010 and trace(30,19) = 101 as in the entries' examples
(the intermediate pairs printed in A228471's example are misprinted; the trace is right). With offset 0 the
term a(n) belongs to the first n+1 letters (a(0) = 2 for the word 0, a(0) = 3 for the word 1).

**Result.** Both conjectures are true for all n. More generally, for every nonempty 0-1 word w the least such c is
given by a backward greedy recursion.

**Argument.** Let the run be (y_{-1}, y_0) = (b, c), (y_0, y_1), ..., (y_{L-1}, y_L), y_L = gcd. Step k sends
(y_{k-2}, y_{k-1}) to (y_{k-1}, y_k); letter 0 means y_{k-2} = q y_{k-1} + y_k with 2y_k <= y_{k-1}, letter 1 means
y_{k-2} = q y_{k-1} - y_k with 2y_k < y_{k-1}. Since 2y_{k-1} <= y_{k-2}, q >= 2 for letter 0 and q >= 3 for
letter 1. In the coordinates t = y_{k-1} - 2y_k >= 0, u = y_k >= 1 the backward step is
(t,u) -> ((q-2)(t+2u) + u, t+2u) for letter 0 and ((q-2)t + (2q-5)u, t+2u) for letter 1: monotone in t, u, q.
So c = t + 2u is smallest with y_L = 1, the smallest y_{L-1} (2 or 3 by the last letter) and the smallest q at every
step; the resulting pairs are realised (b = 2c + y_1 or 3c - y_1). For alternating words, two backward steps act
by (a,b) -> (5a+3b, 2a+b) (pattern 01) or (7a-2b, 3a-b) (pattern 10); both matrices have trace 6 and determinant
-1, so the minima satisfy x(n+4) = 6x(n+2) + x(n), and the first four values are 2, 8, 13, 49 and 3, 5, 19, 31.

**Evidence.**
- Lean (Mathlib): [`A228469_mathlib.lean`](A228469_mathlib.lean). `A228469_conjecture n : IsLeast {c | 0 < c ∧ ∃ b,
  0 < b ∧ tr b c = alt false (n+1)} (A228469 n)` and `A228471_conjecture` (same with `alt true`), `A228469`,
  `A228471` the recurrences as in the entries' names, `tr` the trace. General form `A228469.least_c`.
  `tools/leancheck-mathlib.sh`: OK, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/trace.py`](certificate/trace.py): brute force over c < 6000 reproduces a(0..8) of both entries.
- Outside Lean: none beyond the reading of the definitions.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: both entries still state the characterisation as a conjecture (the g.f. is from
Moses' program); no proof found in the entries, cross-referenced A228470, A228487, A228488, or a web search. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
