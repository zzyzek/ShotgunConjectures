# OEIS A219085: jump points of x^(1/d) form a linear recurrence sequence

**Source.** OEIS [A219085](https://oeis.org/A219085), a(n) = floor((n + 1/2)^3), the jump points of x^(1/3).
Comment (C. Kimberling, 2012): "Conjecture: if d is a positive integer and f(x) = x^(1/d), then the solutions of
J(k) form a linearly recurrent sequence", where J(k) is {f(k)} < 1/2 < {f(k+1)}. A later comment in the entry:
"This conjecture was proved by David Moews; see Problem 21 in 'Unsolved Problems and Rewards'." (OEIS text,
CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True; known (D. Moews, Jan 2013, Kimberling's Problem 21). Reproved here: the solutions are
⌊(n+1/2)^d⌋ = ⌊(2n+1)^d / 2^d⌋, and since (2n+1)^d mod 2^d depends only on n mod 2^(d-1), this is a polynomial
plus a periodic sequence, which satisfies a linear recurrence ((E−1)^(d+1) applied after (E^p − 1)).

**Evidence.**
- Lean (Mathlib): [`A219085_mathlib.lean`](A219085_mathlib.lean), for the entry's sequence (d = 3):
  `A219085_rec` (the entry's order-7 recurrence for every n, with a(n) = ⌊(n+1/2)^3⌋ over ℚ),
  `A219085_quasi` (a(4k+j) is a cubic polynomial in k for each j), `A219085_data`. Axioms: propext,
  Classical.choice, Quot.sound.
- Outside Lean: that the jump points are ⌊(n+1/2)^d⌋ (k is a jump point iff k < (n+1/2)^d < k+1 for some n),
  and general d.

**Review level.** `lean-proof` for d = 3 (the entry's formula and recurrence); general d known (Moews).

**Prior art.** Checked 2026-11-06: C. Kimberling, "Unsolved Problems and Rewards", Problem 21 (marked solved by
D. Moews, Jan 2013, with his argument: polynomial plus periodic sequence). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
