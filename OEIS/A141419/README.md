# OEIS A141419: diagonal of S_N^T S_N (Chebyshev U sums) equals the triangle

**Source.** [A141419](https://oeis.org/A141419) (Roger L. Bagula, Aug 05 2008): "Triangle read by rows: T(n, k) =
A000217(n) - A000217(n - k) with 1 <= k <= n." Comment by L. Edson Jeffery (Jan 20 2012): "Conjecture. Let N=2*n+1
and k=1,...,n. ... Then t(n,k) = [X_N]_(k-1,k-1) ... Hence t(n,k) is the sum of squares t(n,k) =
sum[m=1,...,n (U_(k-1)(cos((2*m-1)*Pi/N)))^2]." (OEIS text, CC BY-SA 4.0, revision #105 of Sep 17 2026, checked
2026-11-06.)

**Reading.** The conjecture is the identity for the diagonal entries; X_N = S_N^T S_N has (k-1, k-1) entry
Σ_m U_{k-1}(cos θ_m)^2 by definition. The closing remark about A057059 (X_N as a combination of unit-primitive
matrices) is a separate statement and is not treated here.

**Result.** True: Σ_{m=1}^{n} U_{k-1}(cos((2m−1)π/N))^2 = k(2n−k+1)/2 = T(n, k) for 1 ≤ k ≤ n.

**Argument.** With θ_m = (2m−1)π/N, U_{k-1}(cos θ) = sin(kθ)/sin θ, so the sum is g(k) = Σ_m sin²(kθ_m)/sin²θ_m.
The identity sin²((k+1)θ) − 2 sin²(kθ) + sin²((k−1)θ) = 2 cos(2kθ) sin²θ gives g(k+1) − 2g(k) + g(k−1) =
2 Σ_m cos(2kθ_m), and the telescoping 2 sin α Σ_{m<n} cos((2m+1)α) = sin(2nα) with α = 2kπ/N (so 2nα = 2kπ − α,
sin α ≠ 0 for 0 < k < N) gives Σ_m cos(2kθ_m) = −1/2. With g(0) = 0, g(1) = n: g(k) = nk − k(k−1)/2.

**Evidence.**
- Lean (Mathlib): [`A141419_mathlib.lean`](A141419_mathlib.lean). `A141419_conjecture`: for 1 ≤ k ≤ n,
  Σ_{m<n} (eval (cos((2m+1)π/(2n+1))) (Polynomial.Chebyshev.U ℝ (k−1)))^2 = A141419 n k, with
  A141419 n k = n(n+1)/2 − (n−k)(n−k+1)/2 as in the OEIS definition. Uses Mathlib's `U_real_cos`. Axioms
  propext, Classical.choice, Quot.sound; no sorry, no native_decide, no warnings; checked with
  `tools/leancheck-mathlib.sh`.
- [`certificate/check.py`](certificate/check.py): floating-point check for n ≤ 40.
- Outside Lean: none for the diagonal identity. The A057059 remark is not treated.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture. The identity is a standard Fejér-kernel
type trigonometric sum, so the result is immediate for a specialist; no write-up of this exact statement was found.
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06). The repo's
OEIS/A212652 (round 12) treats a different comment of this entry.
