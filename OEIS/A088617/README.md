# OEIS A088617: mean number of U steps in a Schröder n-path is ~ n/√2

**Source.** [A088617](https://oeis.org/A088617), T(n,k) = C(n+k,n)·C(n,k)/(k+1), the number of Schröder
paths from (0,0) to (2n,0) (steps U = (1,1), D = (1,−1), H = (2,0), never below the axis) with k U steps.
Comment by David Callan (2008): "Conjecture: The expected number of U's in a Schroeder n-path is
asymptotically sqrt(1/2)*n for large n." (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05.)

**Result.** True. With r(n) = Σ_k T(n,k) (A006318) and U(n) = Σ_k k·T(n,k), exactly
4·U(n+1) = (3n+2)·r(n+1) − n·r(n), and U(n)/(n·r(n)) → √(1/2).

**Argument.** Write T(n,k) = f_k(n)/(k!(k+1)!) with f_k(n) = (n+k)(n+k−1)…(n−k+1), a polynomial in n
that vanishes for n < k. Comparing f_{k+1}(n+2), f_{k+1}(n+1), f_k(n+1), f_{k+1}(n) gives the coefficient
identity (n+3)·T(n+2,k+1) = (2n+3)·(T(n+1,k+1) + 2·T(n+1,k)) − n·T(n,k+1). Summing it with weights 1 and k:
(n+3)·r(n+2) = 3(2n+3)·r(n+1) − n·r(n) and (n+3)·U(n+2) = (2n+3)·(3U(n+1) + 2r(n+1)) − n·U(n). Induction
then gives 4U(n+1) = (3n+2)r(n+1) − n·r(n). Let α = 3+2√2, β = 3−2√2 = 1/α and x(n) = r(n+1)/r(n). Then
(n+3)·x(n+1) = 3(2n+3) − n/x(n), and by induction 2 ≤ x(n) ≤ α and (n+1)(α − x(n)) ≤ 20 (the error map
contracts by a factor β/2 and adds (3α−9)/(n+3)). So x(n) → α, and
U(n+1)/((n+1)·r(n+1)) = ((3n+2) − n/x(n))/(4(n+1)) → (3 − β)/4 = √2/2 = √(1/2).

**Evidence.**
- Lean (Mathlib): [`A088617_mathlib.lean`](A088617_mathlib.lean). `T` is the entry's formula with natural
  division (exact, `T_cast`). Theorems: `A088617_conjecture`:
  `Tendsto (fun n => (∑ k ∈ range (n+1), k * T n k) / (∑ k ∈ range (n+1), T n k) / n) atTop (𝓝 (√(1/2)))`;
  `A088617_total`: 4 U(n+1) = (3n+2) r(n+1) − n r(n); `T_rec`, `r_rec`, `U_rec`, `x_bounds`, `x_tendsto`.
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: brute-force path counts equal T(n,k) for n ≤ 9; the divisibility and `T_rec`
  for n < 80; the exact formula and the r recurrence for n < 800; the `x_bounds` invariant with exact
  rationals for n < 400; mean/n = 0.70440 (n = 100), 0.70677 (n = 800).
- Outside Lean: that T(n,k) counts Schröder n-paths with k U steps (stated in the entry; classical, e.g.
  T(n,k) = C(n+k,2k)·Catalan(k): choose the 2k U/D positions among n+k steps, a Dyck word on them; checked
  by brute force for n ≤ 9).

**Review level.** `rechecked`: the asymptotic statement is proved in Lean for the entry's formula; the
path interpretation of the formula is not formalized.

**Prior art.** New (checked 2026-11-05). Not in google-deepmind/formal-conjectures. The companion
A090981 (ascents, ~(√2−1)n) was proved by V. Roitner (arXiv:2008.02240, vectorial kernel method +
singularity analysis); that paper does not treat the U-step count, and web search found no proof of the
A088617 statement. The route here avoids singularity analysis: an exact two-term formula plus a ratio limit.
