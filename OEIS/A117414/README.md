# OEIS A117414: an Euler triangle without a definition (row sums, columns 1 and 2)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A117414. [A117414](https://oeis.org/A117414)
(P. Barry, 2006), name "An Euler triangle.", data only:
"Conjecture: row sums are the Euler numbers A000364. Second column is A024255. Third column is A117415."

**Reading.** The entry has had no definition since revision #1 (2006): name, data and the conjecture
only. A claim about a triangle given by 45 numbers is ill-posed. The only rule for all rows in the
entry is G. Critzer's g.f. (Apr 2023):
Sum_{n,k} T(n,k) u^k z^n / B(n) = E((u-1)z)/E(-z), with B(n) = (2n)!/2^n = A000680(n) and
E(z) = Sum_n z^n/B(n). It reproduces all 45 data terms. We take it as the definition.
Columns are numbered from 0, so "second column" is k = 1 and "third column" is k = 2.
(Critzer's comment that T(n,k) counts alternating permutations of [2n] with k cyclically alternating
components is a separate conjecture, not addressed here.)

**Result.** Misstated (no definition). With Critzer's g.f. as the definition all three claims are
true: row sums = A000364 (Euler secant numbers), column 1 = A024255 (n times the tangent number
t(2n-1)), column 2 = A117415 (e.g.f. (x tan x - x^2)/8, even powers).

**Argument.** Put t = sqrt(2z). Then z^n/B(n) = t^(2n)/(2n)!, so a series Sum c_n z^n/B(n) is the
even e.g.f. Sum c_n t^(2n)/(2n)!, and T(n,k) is (2n)! times the coefficient of u^k t^(2n). Also
E(z) = cosh(sqrt(2z)), so E(-z) = cos t.
- u = 1: the g.f. is E(0)/E(-z) = 1/cos t = sec t = Sum A000364(n) t^(2n)/(2n)!.
- Coefficient of u: z E'(-z)/E(-z). From E(w) = cosh s with s = sqrt(2w), E'(w) = sinh(s)/s, and at
  w = -z, s = i t, so E'(-z) = sin(t)/t. The coefficient is (t^2/2)(sin t/t)/cos t = (t tan t)/2,
  the e.g.f. of A024255 (even part of x tan(x)/2), i.e. T(n,1) = n t(2n-1).
- Coefficient of u^2: z^2 E''(-z)/(2 E(-z)), with E''(w) = cosh(s)/s^2 - sinh(s)/s^3, so
  E''(-z) = -cos(t)/t^2 + sin(t)/t^3 and the coefficient is (t^4/8)(tan(t)/t^3 - 1/t^2)
  = (t tan t - t^2)/8, the e.g.f. of A117415.

**Evidence.**
- `certificate/check.py` (exact rationals, standard library): expands the g.f. to row 16, checks the
  45 data terms, and the three identities for rows 0..16 against sec/tan numbers computed from
  sec * cos = 1 and tan = sin * sec; output in `certificate/check.log`.
- Lean: [`A117414_mathlib.lean`](A117414_mathlib.lean), checked (axioms propext, Classical.choice,
  Quot.sound). T is defined from Critzer's g.f. as a series in (Polynomial ℚ)⟦z⟧ (`G`, with
  `G * E(-z) = E((u-1)z)`), sec = cos⁻¹ and tan = sin * sec in ℚ⟦x⟧ (Mathlib `PowerSeries.cos/sin`).
  `A117414_main`: for every n, Sum_k T(n,k) = (2n)! [x^(2n)] sec, T(n,1) = n (2n-1)! [x^(2n-1)] tan,
  T(n,2) = (2n)! [x^(2n)] (x tan x - x^2)/8. Proof through the ring map z -> x^2/2
  (`expand 2 ∘ rescale (1/2)`), which sends E(-z) to cos.
- Outside Lean: none beyond the reading (Critzer's g.f. as the definition of the triangle).

**Review level.** `lean-proof` (Lean, Mathlib) for the three identities under Critzer's g.f.; the 45 data terms
are matched by `certificate/check.py`.

**Prior art.** Verdict `misstated` (immediate). The identities follow from Critzer's g.f. at once;
Elkies (arXiv:math/0101168, Lemma 4, eq. (53)) counts cyclically alternating permutations of [2m]
as m t(2m-1) = A024255(m), which is column 1 under Critzer's combinatorial reading. Sources:
[OEIS A117414 and history](https://oeis.org/history?seq=A117414) (fetched 2026-11-05);
[N. D. Elkies, On the sums Sum((4k+1)^(-n))](https://arxiv.org/abs/math/0101168).
Searched: OEIS entry, history and cross-references (A000364, A024255, A117415, A000680),
google-deepmind/formal-conjectures (tree listing: no file for A117414), 2026-11-05.
