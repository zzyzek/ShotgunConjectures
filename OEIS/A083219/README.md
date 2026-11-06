# OEIS A083219: roots of x^n - x^(n-1) - ... - 1 in the left half-plane

**Source.** [A083219](https://oeis.org/A083219), a(n) = n − 2⌊n/4⌋. The conjecture says a(n) counts the roots of
x^n − x^(n−1) − … − x − 1 in the left half-plane.

**Reading.** As written, the claim is off by one in its indexing. The count for degree n+1 equals a(n).

**Result.** True with the index shift. For every n, x^(n+1) − x^n − … − x − 1 has n − 2⌊n/4⌋ roots with Re < 0.

**Argument and evidence.** Proved together with A129756: see [OEIS/A129756](../A129756/README.md). The Lean
theorem is `A129756.A083219_roots` in `OEIS/A129756/A129756_mathlib.lean`.

**Review level.** `lean-proof`. Outside Lean: the index-shift reading.

**Prior art.** As for A129756 (checked 2026-11-06).
