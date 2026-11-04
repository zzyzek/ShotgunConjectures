# OEIS A225001: floor(1/frac(e^(4/(5n)))) = A047203(n) for n > 1

**Source.** OEIS [A225001](https://oeis.org/A225001), now a dead entry ("Duplicate of A047203").
Its Mathematica program defines a(n) = floor(1/FractionalPart[(e^(4/5))^(1/n)]). Conjecture
(R. J. Mathar, 2013): "a(n) = A047203(n), n>1." A047203 = numbers ≡ 0, 2, 3, 4 (mod 5),
A047203(n) = floor((5n-2)/4). (OEIS text, CC BY-SA 4.0.)

**Result.** True. (The scan recorded only that the entry was merged; the identity is proved here.)

**Argument.** Let u = 4/(5n). For n ≥ 2, u ≤ 2/5 < log 2, so frac(e^u) = e^u - 1. For u > 0,
1/u - 1/2 < 1/(e^u - 1) < 1/u - 1/2 + u/12 (from the Bernoulli expansion; both bounds are
standard). Hence 1/frac(e^u) = 5n/4 - 1/2 + δ with 0 < δ < u/12 = 1/(15n) ≤ 1/30. The number
5n/4 - 1/2 = (5n-2)/4 has fractional part 0, 1/4, 1/2 or 3/4, so adding δ < 1/4 does not cross an
integer: a(n) = floor((5n-2)/4) = A047203(n). (n = 1: a(1) = 4 ≠ A047203(1) = 0, hence "n > 1".)

**Evidence.**
- `certificate/a225001.py` (mpmath, 60 digits): a(n) = floor((5n-2)/4) for 2 ≤ n ≤ 10^5; a(1) = 4.
- Lean (Mathlib): [`A225001_mathlib.lean`](A225001_mathlib.lean), `A225001_main`: for every n >= 2, ⌊1/frac(exp(4/5)^(1/n))⌋ = (5n - 2) div 4 = A047203(n). Uses Mathlib's Taylor bounds 1 + u + u²/2 ≤ e^u ≤ 1 + u + u²/2 + 2u³/9 (0 ≤ u ≤ 1) in place of the Bernoulli-expansion bounds. Outside Lean: none.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** The bounds 1/u - 1/2 < 1/(e^u - 1) < 1/u - 1/2 + u/12 for u > 0
(real analysis).

**Prior art.** Partly known. [OEIS A225001](https://oeis.org/A225001) (fetched 2026-11-04) is dead, merged as a duplicate of [A047203](https://oeis.org/A047203), so the editors accepted the identity; A047203 has no proof or mention of it. Searched: entry, OEIS cross-reference search, A047203. Nothing to send to OEIS. (Prior-art review 2026-11-04.)
