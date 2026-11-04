# OEIS A192205: a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n

**Source.** OEIS [A192205](https://oeis.org/A192205): a(n) = sum of absolute values of the
coefficients of (1-x-x^2+x^3)^n. Conjecture: "limit a(n)^(1/n) = 16*sqrt(3)/9 = 3.079201...,
which is substantiated by the observation that the sums of the coefficients squared in
(1-x-x^2+x^3)^n equals binomial(4n,n)." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Let P(x) = 1 - x - x^2 + x^3 = (1-x)^2(1+x), l1 = a(n), l2 = (sum c_k^2)^(1/2) for
P^n. Cauchy–Schwarz over the 3n+1 coefficients gives l2 ≤ l1 ≤ √(3n+1) l2, so
lim l1^(1/n) = lim l2^(1/n) if the latter exists. By Parseval, l2^2 = (1/2π) ∫ |P(e^(it))|^(2n) dt,
and the L^(2n) norm of |P| on the circle tends (as n → ∞, after taking the 1/(2n)-th power) to its
sup norm. |P(e^(it))|^2 = |1-e^(it)|^4 |1+e^(it)|^2 = 64 s^2 (1-s) with s = sin^2(t/2), maximal at
s = 2/3 with value 256/27, so sup |P| = 16/(3√3) = 16√3/9.
(The entry's identity sum c_k^2 = C(4n,n), checked here for n < 200, gives the same limit
(256/27)^(1/2) via Stirling, but it is not needed.)

**Evidence.**
- `certificate/a192205.py`: sum c_k^2 = C(4n,n) for n < 200; a(n)^(1/n) = 3.0809 at n = 1200
  (limit 3.0792, convergence like (3n+1)^(1/(2n))).
- Lean (Mathlib): [`A192205_mathlib.lean`](A192205_mathlib.lean), `A192205_main`: a(n)^(1/n) → 16√3/9, with a(n) the sum of |coefficients| of (1 - X - X^2 + X^3)^n in Z[X]. Uses Mathlib's polynomial Parseval identity (`Polynomial.sum_sq_norm_coeff_eq_circleAverage`), Cauchy–Schwarz, and the lower bound |P(z0)|^n ≤ a(n) at z0 = -1/3 + (2√2/3)i. Outside Lean: none (the side identity sum c_k^2 = C(4n,n) is not used).

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** Parseval for trigonometric polynomials, L^p → L^∞ norm convergence
on the circle (or the identity sum c_k^2 = C(4n,n) plus Stirling).

**Prior art.** New to OEIS, immediate. [OEIS A192205](https://oeis.org/A192205) (fetched 2026-11-04) still states the conjecture; the sister A084611 likewise. The proof is the two-line l2/l1 comparison using the entry's own binomial(4n,n); it is also an instance of the spectral-radius formula in the Wiener algebra (limit = max of |P| on the unit circle). Searched: entry, OEIS cross-reference search, edit history, web for the general limit. Worth an OEIS comment. (Prior-art review 2026-11-04.)
