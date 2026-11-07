# GEO A33.2: the Lamé oval |x|^2.001 + |y|^2.001 = 1 has five-point hyperbolas

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry* (1991),
Section A33 (conics through five points). Paraphrase: Reznick asks what can be said about an
infinite set S, for instance a union of rectifiable curves, if every five-point subset of S
determines an ellipse (or, respectively, a hyperbola). The book adds the suggestion that
|x|^2.001 + |y|^2.001 = 1 yields only ellipses.

**Reading.** Two parts: the open-ended "describe such sets", and the specific suggestion about
the oval. Only the specific suggestion is settled here.

**Result.** The suggestion is false. Take p = 2001/1000 and the five points on the oval with
y_k = k/1000 and x_k = (1 − y_k^p)^{1/p}, k = 1..5 (all near the vertex (1,0), on one side of
it). Their conic a x² + b xy + c y² + d x + e y + f = 0 is a nondegenerate hyperbola, with
b² − 4ac ≈ 5.169·10^{−56} > 0. The same holds for y_k = k/10^4 and k/10^5. The scales
k/10 and k/100 give ellipses.

**Argument.** Near (1,0) the oval is u ≈ y^p/p with u = 1 − x. Georgiou (below) proves that
any five points on a power curve u = a y^p with p > 2 and y > 0 determine a hyperbola. As the
five points shrink toward the vertex, the oval's own five-point conic converges to that case.
The certificate does not use this limit argument. It computes the conic coefficients as signed
5×5 minors (Cramer's rule) in 120-digit interval arithmetic. The interval for b² − 4ac is
strictly positive, and the interval for the 3×3 conic determinant excludes 0.

**Evidence.**
- `certificate/lame.py`, output `certificate/lame.out` (mpmath `iv`, 120 digits; exits 0
  only if some scale gives a certified nondegenerate hyperbola).
- Lean: none. The points have transcendental coordinates. A Lean proof would need verified
  interval bounds for x^{1/p} and an interval evaluation of a degree-20 polynomial with
  about 60 digits of cancellation.
- Outside Lean: the whole computation (rigorous interval arithmetic, not formalised).

**Review level.** `rechecked` (independent interval computation of the published claim).

**Prior art.** Checked 2026-11-06: G. M. Georgiou, *Five-point hyperbolas on power curves and
near Lamé-oval vertices*, arXiv 2608.00790 (August 2026). It proves the power-curve statement
and says that profiles contracted toward an axial vertex of the Lamé oval eventually give
hyperbolas, so the p = 2.001 suggestion fails. Symmetric profiles straddling the vertex give
ellipses. The abstract gives no explicit points. Web search; google-deepmind/formal-conjectures
(HEAD 2026-11-05, no entry). The general question (describe all such S) stays open.
