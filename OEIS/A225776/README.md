# OEIS A225776: Hankel determinants of sum_j C(k,j)^r are 2^n times a positive odd integer

**Source.** [A225776](https://oeis.org/A225776), Zhi-Wei Sun (2013): a(n) is the Hankel determinant
|f(i+j)|_{0<=i,j<=n} of the Franel numbers f(k) = A000172(k). Comment: "Conjecture: a(n)/6^n is always a positive
odd integer. Moreover, for any integers r > 1 and n >= 0, the number a(r,n)/2^n is a positive odd integer, where
a(r,n) denotes the Hankel determinant |f(r,i+j)|_{i,j=0,...,n} with f(r,k) = Sum_{j=0..k} C(k,j)^r."
(OEIS text, CC BY-SA 4.0, cached entry read 2026-11-07.)

**Result.** True for all r >= 2 and n >= 0.
- r = 3, the first sentence: Zhu and Sun, IJNT 14 (2018), Theorem 1.1 (known; the entry says so since Sep 2026).
- a(r,n)/2^n is an odd integer for r >= 3: Zhu and Sun, Theorem 1.1 (known). For r = 2, f(2,k) = C(2k,k) and
  a(2,n) = 2^n (classical).
- a(r,n) > 0 for r >= 4: new here (Zhu and Sun prove positivity only for r = 3).

**Argument (positivity, all r >= 2).** f(r,k) is the constant term of L^k with the Laurent polynomial
L = (1+x_1)...(1+x_{r-1})(1 + 1/(x_1...x_{r-1})): choosing x_i^{a_i} from (1+x_i)^k and (x_1...x_{r-1})^{-b}
from the last factor gives coefficient C(k,a_1)...C(k,a_{r-1})C(k,b), and the constant term forces a_i = b.
Put x_i = e^{i t_i}. Since 1 + e^{it} = 2 cos(t/2) e^{it/2}, and the half-angle phases cancel against
1 + e^{-i(t_1+...+t_{r-1})} = 2 cos(s/2) e^{-is/2} with s = t_1+...+t_{r-1}, L takes the real value
L(t) = 2^r cos(s/2) cos(t_1/2)...cos(t_{r-1}/2) on the torus. Every exponent of x_i in L^k lies in [-k, k], so for
N = 2n+1 and all k <= 2n the constant term equals the average over the grid G of N-th roots of unity:
f(r,k) = N^{-(r-1)} Sum_{g in G} L_g^k, with L_g real. Hence the Hankel matrix is
H = N^{-(r-1)} Sum_g v_g v_g^T with v_g = (1, L_g, ..., L_g^n), and by Cauchy-Binet
det H = N^{-(r-1)(n+1)} Sum over (n+1)-subsets S of G of Prod_{a<b in S} (L_a - L_b)^2 >= 0.
The grid points t = (2 pi m/N, 0, ..., 0), m = 0..n, give L = 2^{r-1}(1 + cos(2 pi m/N)), which are n+1 distinct
values, so one summand is positive and det H > 0. (Equivalently: f(r,.) is the moment sequence of the image of
Haar measure under L, a measure with infinite support.)

**Evidence.**
- Lean (Mathlib): [`A225776_mathlib.lean`](A225776_mathlib.lean), theorem `A225776_pos`: for all r >= 2 and
  n >= 0, 0 < det [f(r, i+j)]_{0<=i,j<=n} over ℤ, with f(r,k) = Sum_{j=0..k} C(k,j)^r. Axioms propext,
  Classical.choice, Quot.sound. The Lean proof avoids the roots-of-unity grid and the cosines: in Laurent
  polynomials, L(1/x) = L(x), so c^T H c = CT(Q(x) Q(1/x)) with Q = Sum c_i L^i is the sum of the squared
  coefficients of Q (library `OpenProblemsLib.MomentHankel.hankel_posDef`, guide `lib/docs/moment-hankel.md`);
  Q = 0 forces c = 0 because L at x_1 = t, x_2 = ... = 1 equals 2^{r-2}(2 + t + 1/t), injective on t = 1, 2, ...
- [`certificate/check.py`](certificate/check.py): the grid-average formula for r = 2..4, k < 9; a(r,n) > 0 and
  a(r,n)/2^n odd for r = 2..7, n = 0..8 (exact sympy determinants).
- Outside Lean: the oddness of a(r,n)/2^n for r >= 3 and the r = 3 statement a(n)/6^n odd (Zhu-Sun Theorem 1.1,
  cited); a(2,n) = 2^n (classical).

**Review level.** `lean-proof` for positivity (all r >= 2); oddness cited to Zhu-Sun.

**Prior art.** Checked 2026-11-07. Zhu-Sun (arXiv:1609.06810, IJNT 2018) Theorem 1.1: "2^{-n}|f^{(r)}_{i+j}| is
an odd integer" for r >= 3 and positivity only for r = 3. Web search found no positivity proof for r >= 4 and no
statement that sum_j C(k,j)^r is a moment sequence for general r. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).

**Open strengthening.** Kotesovec's conjecture a(n)^{1/n^2} -> 9/4 (r = 3, Sep 2026) is not proved here. The
measure above suggests the route (not checked in detail): for r = 3 the range of L is [-1, 8] (numerical minimum
-1, maximum 8, matching the roots of the Franel recurrence), whose logarithmic capacity is 9/4; for a measure in
the Stahl-Totik class Reg, Hankel determinants satisfy H_n^{1/n^2} -> cap(support), which would give 9/4.
Missing: a proof that the image measure is regular (e.g. positive density a.e. on [-1, 8]).
