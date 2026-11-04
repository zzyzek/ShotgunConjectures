# OEIS A197521: the constant 3.52133782... is 3 plus the constant of A197383

**Source.** OEIS [A197521](https://oeis.org/A197521): least x > 0 with cos(πx/2) = cos²(πx/3).
Conjecture: "the constant here, 3.52133782..., is 3 plus the constant in A197383, the latter being
the least t>0 satisfying sin(Pi*t/6)=(sin Pi*t/3)^2." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Put x = t + 3 and s = sin(πt/6), θ = πt/6. Then cos(πx/2) = sin(3θ) = 3s - 4s^3 and
cos²(πx/3) = cos²(2θ) = (1 - 2s²)². The first equation becomes
4s^4 + 4s^3 - 4s^2 - 3s + 1 = (s + 1)(4s^3 - 4s + 1) = 0. The A197383 equation
sin θ = sin²(2θ) = 4s²(1 - s²) becomes s(4s^3 - 4s + 1) = 0.
- No root with x ∈ (0, 3]: there t ∈ (-3, 0], s ∈ (-1, 0]; s = -1 only at x = 0, and
  g(s) = 4s^3 - 4s + 1 > 0 on [-1, 0] (minimum at s = -1/√3, value 1 + 8/(3√3) > 0).
- For t > 0 the least root of either equation comes from the least θ > 0 with g(sin θ) = 0, i.e.
  θ = arcsin(s1) with s1 ≈ 0.2696 the least positive root of g (s = -1 needs θ = 3π/2, s = 0 needs
  θ = π, both later). So both least roots are t0 = (6/π) arcsin(s1) = 0.52133782957..., and the
  A197521 constant is 3 + t0.

**Evidence.**
- `certificate/a197521.py` (mpmath, 50 digits): t0 from the cubic, both trigonometric equations
  vanish at t0 resp. 3 + t0 to 50 digits, no sign change of the A197521 function on (0, 3.52].
- Lean (Mathlib): [`A197521_mathlib.lean`](A197521_mathlib.lean), `A197521_main`: there is t0 with t0 = least t > 0 satisfying sin(πt/6) = sin(πt/3)^2 and 3 + t0 = least x > 0 satisfying cos(πx/2) = cos(πx/3)^2 (`IsLeast` for both). Outside Lean: none (the decimal value 3.52133782... is not part of the claim and is not checked in Lean).

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** Triple/double angle identities, arcsin monotonicity; the polynomial
factorisations are elementary.

**Prior art.** New to OEIS, elementary. [OEIS A197521](https://oeis.org/A197521) (fetched 2026-11-04) still states the conjecture (2025 edit only adds irrationality); A197383 does not mention it. Searched: entry, OEIS cross-reference search, edit history, sister A197383. Worth an OEIS comment. (Prior-art review 2026-11-04.)
