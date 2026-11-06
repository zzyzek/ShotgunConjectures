# OEIS A192023: the determinant-2n matrix count does not match; a linear count does

**Source.** OEIS [A192023](https://oeis.org/A192023) (Wiener index of the comb graph with 2n
nodes, a(n) = n(2n² + 6n − 5)/3), comment by Clark Kimberling (Mar 31 2012): "Conjecture: for
n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in {1,2,...,n} and
determinant 2n." (OEIS text, CC BY-SA 4.0.)

**Reading.** Literal: count matrices [[w, x], [y, z]] with w, x, y, z ∈ {1, …, n} and
wz − xy = 2n. Allowing |det| = 2n only doubles the count and does not help.

**Result.** False as stated, already at n = 3: the matrices with entries in {1, 2, 3} and
determinant 6 are [[3, 1], [3, 3]] and [[3, 3], [1, 3]], two of them, while A192023(1) = 1.
The two sides differ for every 3 ≤ n ≤ 120 (count 2, 9, 16, 33, 42, 69, … against
1, 10, 31, 68, 125, 206, …). The determinant count is not even monotone (228 at n = 12, 180 at n = 13).

The comment is a misattribution. Kimberling's own guide in [A211795](https://oeis.org/A211795)
pairs A192023 with the linear relation w = −x + y + z + 2, and that version holds:

  #{(w, x, y, z) ∈ {1, …, n}⁴ : w + x = y + z + 2} = A192023(n − 1) for all n ≥ 2,

with A192023(m) the Wiener index of the comb graph with 2m nodes (the entry's definition).
This is proved in Lean for all n, together with the entry's formula a(m) = m(2m² + 6m − 5)/3.

equivalently A192023(n − 2) counts 4-tuples in {1, …, n − 1} with w + x = y + z + 2 (n ≥ 3).
A search over 2268 readings (entry ranges {0..k}, {1..k}, {−k..k} with k = n − 3, …, n + 3;
determinant, |determinant| or permanent equal to αn + β, 0 ≤ α ≤ 3, −4 ≤ β ≤ 4;
`certificate/search2.py`) finds no determinant or permanent reading that matches for
3 ≤ n ≤ 10.

**Argument.** Counterexample: wz − xy = 6 with entries ≤ 3 forces wz = 9 (w = z = 3) and
xy = 3, so (x, y) ∈ {(1, 3), (3, 1)}.
Corrected statement: with r(s) = #{(w, x) ∈ {1..n}² : w + x = s} = n − |s − n − 1| for
2 ≤ s ≤ 2n, the count is Σ_s r(s) r(s − 2). For n ≥ 2 and m = n − 2 the terms
s = 4..n + 1 give Σ_{t=1}^{m} t(t + 2), s = n + 2 gives (n − 1)², and s = n + 3..2n give
Σ_{u=1}^{m} u(u + 2) again. With Σ_{t=1}^{m} t(t + 2) = m(m + 1)(2m + 7)/6 the total is
(m + 1)(2m² + 10m + 3)/3 = a(m + 1) = a(n − 1). For n = 1 both sides are 0.
Wiener index: with spine vertices (i, 0) and teeth (i, 1), the distance is |i − j| + s + t for
i ≠ j and [s ≠ t] for i = j. Summing over the four (s, t) gives 4|i − j| + 4 (i ≠ j) or 2
(i = j), and Σ_{i,j<m} |i − j| = (m³ − m)/3, so half the ordered sum is
m + 2(m³ − m)/3 + 2(m² − m) = a(m).

**Evidence.**
- Lean (Mathlib): [`A192023_mathlib.lean`](A192023_mathlib.lean). `A192023_main`: for n ≥ 2
  the count equals `A192023_wiener (n − 1)`, the Wiener index of `A192023_comb (n − 1)`
  (Mathlib `SimpleGraph.dist`, half the sum over ordered pairs). Built from `A192023_linear`
  (count = a(n − 1), n ≥ 1), `A192023_dist` (graph distance = explicit formula) and
  `A192023_wiener_eq` (Wiener index = a(n), n ≥ 1). Axioms propext, Classical.choice,
  Quot.sound; zero warnings. Outside Lean: the modelling of the comb graph |_|_|…|_| as
  `A192023_comb` (vertices Fin n × Fin 2, spine path plus one tooth per spine vertex).
- Lean (core): [`A192023.lean`](A192023.lean). `A192023_det_counterexample` (n = 3: count 2,
  a(1) = 1), `A192023_det_mismatch_<n>` (sides differ for 3 ≤ n ≤ 10), `A192023_linear_<n>`
  (corrected identity for 1 ≤ n ≤ 15, closed form). No axioms. Outside Lean: none for the
  disproof.
- `certificate/count.py` (literal reading, 3 ≤ n ≤ 120), `certificate/search.py`,
  `certificate/search2.py` (alternative readings), `certificate/linear.py` (linear count).

**Review level.** `lean-proof` (disproof in core Lean; corrected statement for all n, with
A192023 as the Wiener index of the comb graph, in Mathlib).

**Prior art.** The OEIS entry still lists the comment as a conjecture (checked 2026-11-06;
history shows only a 2017 formatting edit of the comment). The linear relation is Kimberling's
own table in A211795 (2012), so the corrected statement is known; the falsity of the
determinant wording is not recorded there. google-deepmind/formal-conjectures (HEAD 2026-11-05)
has no file for A192023.
