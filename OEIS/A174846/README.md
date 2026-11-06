# OEIS A174846: |a(n)/n!|^(-1/n) tends to pi/4 = 0.7853...

**Source.** OEIS [A174846](https://oeis.org/A174846) (Paul D. Hanna, Jan 24 2011): e.g.f. AGM(1, exp(4x)).
Comment: "Conjecture: limit |a(n)/n!|^(-1/n) = r exists and is finite with r<0.8..." and the question "What is the
radius of convergence of the e.g.f.?". Vaclav Kotesovec (Sep 27 2019) adds r = Pi/4 and the form
e^(4x) Pi / (2 EllipticK(1 - e^(-8x))), without a proof. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: the limit exists and equals pi/4 = 0.78539... < 0.8. Asymptotically
a(n)/n! = -pi (4/pi)^n Re(i^(1-n)) / (n log^2 n) (1 + o(1)) for odd n, and |a(n)/n!| is of exact order
(4/pi)^n / (n^2 log^2 n) for even n.

**Argument.** Let f(x) = AGM(1, e^(4x)) with the principal AGM, analytic in z = e^(4x) on C minus (-inf, 0].
1. *Radius.* For |x| < pi/4, |Im 4x| < pi, so e^(4x) avoids (-inf, 0] and f is analytic: radius >= pi/4.
   At x0 = i pi/4, z = -1. Writing AGM(1,z) = sqrt(z) AGM(1, k') with k' = (1+z)/(2 sqrt z) and
   AGM(1,k') = pi/(2K(k)), K(k) = A(k'^2) log(4/k') + B(k'^2) with A, B analytic, A(0) = 1, B(0) = 0 (classical
   expansion of the complete elliptic integral at k' = 0), one gets near x0, with d = x - x0 and k' = 2i d (1 + O(d)),
   f(x) = (pi i / 2) / (log(-2i/d) + O(d log d)). This is not analytic at x0 (f -> 0 while f' is unbounded),
   so the radius is exactly pi/4, and limsup |a(n)/n!|^(1/n) = 4/pi.
2. *Delta-analyticity.* On the circle |x| = pi/4 only x0 and its conjugate have |Im 4x| = pi; every other point has
   a neighbourhood where the principal branch is analytic. The local form in step 1 continues to a slit
   neighbourhood of x0 (and of its conjugate). By compactness f is analytic in a Delta-domain at +-x0 of radius
   pi/4 + eta.
3. *Transfer* (Flajolet-Odlyzko, logarithmic singularities, Flajolet-Sedgewick *Analytic Combinatorics* VI.2).
   With w = x/x0, the singular part at x0 is (pi i/2) / (log(8/pi) + log(1/(1-w))) + ..., whose w^n coefficient is
   -(pi i/2)/(n log^2 n)(1 + O(1/log n)); adding the conjugate gives the odd-n formula above, with
   |Re(i^(1-n))| = 1 for odd n.
4. *Even n.* The even part of f is E(x) = f(x)(1 + e^(-4x))/2, because f(-x) = e^(-4x) f(x) (AGM is homogeneous).
   At x0, 1 + e^(-4x) = 4d + O(d^2), so E's singular part is of type (1 - w)/log(1/(1-w)), with coefficients of exact
   order (4/pi)^n/(n^2 log^2 n); the conjugate contributions do not cancel for even n (their sum is
   +- 2 pi (pi/4)^(1-n) times a real sequence of that order).
Hence |a(n)/n!|^(1/n) -> 4/pi along both parities, and r = pi/4.

**Evidence.**
- [`certificate/agm.gp`](certificate/agm.gp), [`certificate/agm.out`](certificate/agm.out): AGM iteration on power
  series to x^1204 at 600 digits (matches the entry's a(0..20) exactly). |a(n)/n!|^(-1/n) (4/pi) is 1.0086 (odd) and
  1.0141 (even) at n = 1200..1203, consistent with the factors (n log^2 n)^(1/n) and (n^2 log^2 n)^(1/n). The
  scaled value a(n)/n! (pi/4)^n n log^2 n alternates -1.97, +1.97 on odd n (slowly moving toward -+pi as the
  log corrections fade) and is of order 1/n on even n.
- Lean: none. Mathlib has the real AGM of two nonnegative reals but no complex AGM, complete elliptic
  integrals or singularity-analysis transfer theorems.
- Outside Lean: the whole argument (steps 1-4).

**Review level.** `agent`.

**Prior art.** Checked 2026-11-06. The value r = pi/4 is Kotesovec's comment in the entry (2019), stated without
proof; the existence of the limit (which needs the even-n analysis) is not addressed there. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
