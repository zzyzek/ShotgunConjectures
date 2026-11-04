# OEIS A100682: exception list of Greathouse's formula is incomplete

**Source.** OEIS [A100682](https://oeis.org/A100682), comment by Charles R Greathouse IV (May 2012):
"Conjecture: a(n) = floor((n − 3/2)/24^(1/4)) for n not in {0, 1, 6, 17, 2403, 5318}."
(OEIS text, CC BY-SA 4.0.)

**Reading.** The entry defines a(n) = floor(C(n+3,4)^(1/4)). With that index the formula is
off by a shift of 3 almost everywhere; the reading that reproduces the stated exceptions
exactly (6, 17, 2403, 5318 below 6000) is floor(C(n,4)^(1/4)) = floor((n − 3/2)/24^(1/4)).
That is the reading used here.

**Result.** False. n = 634027531 (OEIS index 634027528) is a further exception:
floor(C(n,4)^(1/4)) = 286454272 but floor((n − 3/2)/24^(1/4)) = 286454273.
More: 1705327318, 55292025086, … (near continued-fraction convergents of 384^(1/4)).

**Evidence.**
- Lean: [`A100682.lean`](A100682.lean) checks the integer inequalities at n = 634027531.
  Outside Lean: the equivalence b ≤ (n − 3/2)/24^(1/4) ⇔ 384·b^4 ≤ (2n − 3)^4 (monotonicity of x⁴).
- `certificate/a100682_cf.py` finds the exceptions from the convergents.
- Lean (Mathlib): [`A100682_mathlib.lean`](A100682_mathlib.lean), `A100682_main`: at n = 634027531 (not in the list), ⌊C(n,4)^(1/4)⌋ = 286454272 and ⌊(n - 3/2)/24^(1/4)⌋ = 286454273 with `Real.rpow` and `Int.floor`. The monotonicity step is proved there; nothing outside Lean (under the reading above).

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** New: no source gives further exceptions; [A100682](https://oeis.org/A100682) still lists {0, 1, 6, 17, 2403, 5318}. Searched OEIS entry, references and history, web. Checked 2026-11-04.
