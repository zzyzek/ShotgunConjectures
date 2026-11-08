# OEIS A109381: exceptions to a(n) -> infinity are sparse; the conjecture implies Brocard finiteness (partial)

**Source.** [A109381](https://oeis.org/A109381): a(n) = maximum digit of n^2 written in factorial base. Comment:
"Conjecture: lim_{n->infinity} a(n) = infinity. If true, convergence is very slow, since a(1183893) = 1." (Entry
text via the scan cache, 2026-11-07.)

**Reading.** Digit i (i >= 1) of N is floor(N / i!) mod (i+1); N = sum_i digit_i * i!. The conjecture says: for
every B only finitely many n have a(n) <= B.

**Result (partial; the conjecture stays open).**
1. For every B and k >= 1 there is K with #{n < X : a(n) <= B}^k <= K X^2 for all X; so the exceptions number
   O(X^(2/k)) for every k, and a(n) -> infinity along a set of density 1.
2. If the conjecture holds, Brocard's equation n^2 = k! + 1 has finitely many solutions. So the conjecture is at
   least as hard as Brocard's problem (open; finiteness is known only under abc, Overholt 1993).
3. Computation: the n with a(n) <= 1 and n^2 < 31! (n < 9.06*10^16) are exactly 0, 1, 3, 5, 11, 12, 27, 29, 71, 72,
   213, 215, 603, 635, 1917, 1183893. With a(n) <= 2 and n^2 < 20! there are 140 values, the largest 500048435.

**Argument.**
1. The factorial-base digits of N < m! determine N (N mod (i+1)! = N mod i! + i! * digit_i), so at most (B+1)^m
   numbers below m! have all digits <= B. For n < X take the least m with X^2 <= m!; then (m-1)! < X^2 and
   count^k <= (B+1)^(km) = c * c^(m-1) <= c * c^c * (m-1)! < c^(c+1) X^2 with c = (B+1)^k, using
   c^j <= c^c j! for all j.
2. For k >= 2, k! + 1 has digit 1 at positions 1 and k and 0 elsewhere (i! divides k!, and (i+1) divides k!/i!
   for 2 <= i < k). So n^2 = k! + 1 forces a(n) <= 1, and finiteness of {n : a(n) <= 1} bounds Brocard solutions.
3. `lowdig.c` enumerates all N < m! with factorial digits <= B (2^30 numbers for B = 1, m = 31) in 128-bit
   arithmetic and keeps the perfect squares (modular filters, then an exact integer square root).

**Evidence.**
- Lean (Mathlib): [`A109381_mathlib.lean`](A109381_mathlib.lean). `A109381_sparse` (item 1), `A109381_density_zero`
  (for all B, eps > 0, eventually #{n < X : a(n) <= B} <= eps X), `fact_base_count`,
  `conjecture_implies_brocard_finite` and `a_brocard` (item 2). `a n` is the max of the digits of n^2 over
  i <= n^2 (`a_le_iff`: equivalent to all digits <= B). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings;
  axioms at most propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- [`certificate/lowdig.c`](certificate/lowdig.c), outputs [`certificate/b1_m31.txt`](certificate/b1_m31.txt) and
  [`certificate/b2_m20.txt`](certificate/b2_m20.txt) (item 3).
- Outside Lean: item 3 (computation only).

**Review level.** `lean-proof` for items 1-2; `agent` for item 3.

**Prior art.** Checked 2026-11-07: OEIS entry (b-file to n = 20954; conjecture still stated), formal-conjectures and
oeis-lean-proofs clones (no A109381). The B = 1 case is the question of squares that are sums of distinct
factorials; we did not find a published finiteness result. Brocard's problem: Berndt, Galway (2000) found no further
solutions with k <= 10^9; Overholt (1993) finiteness under abc.
