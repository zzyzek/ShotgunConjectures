# OEIS A228934: the optimal ascending continued fraction of √44 − 6 follows a two-step recurrence

**Source.** OEIS [A228934](https://oeis.org/A228934) (offset 1): optimal ascending continued fraction
(OACF, defined in A228929) of √44 − 6: 2, 4, 15, −99, −199, −800, −79201, −316808, ... Conjecture
(G. Artico, Sep 2013): "The terms of the expansion of sqrt(x) are all negative starting from a(4) and
satisfy these recurrence relations for n>=3: a(2n) = 4*a(2n-1) - 4 and a(2n+1) = -2*a(2n-1)^2 + 1."
(OEIS text, CC BY-SA 4.0; still stated on 2026-11-05. "sqrt(x)" means the expansion of √44 − 6.)

**Reading.** A228929's algorithm: z_0 = x − ⌊x⌋; r_k = round(1/|z_k|), a(k+1) = sign(z_k) r_k,
z_(k+1) = |z_k| r_k − 1. No 1/|z_k| is a half-integer here, so the rounding convention does not matter.

**Result.** True.

**Argument.** Let s = √44 and ε = 199 + 30s (a unit: 1/ε = 199 − 30s, ε + 1/ε = 398). Direct
computation: z_0 = s − 6, z_1 = 2s − 13, z_2 = 8s − 53, z_3 = 120s − 796 = −4/ε, with terms 2, 4, 15, −99
(1/|z_3| = ε/4 = 99.4997...), and z_4 = 78803 − 11880s = 1/ε² − 2/ε.
Two-step lemma: let G ≥ 11 with G + 1/G = 2t, t ∈ ℤ, and z_k = 1/G² − 2/G < 0. Then
1/|z_k| = G²/(2G−1) = t + (G−1)²/(2G(2G−1)), so r_k = t, a(k+1) = −t and
z_(k+1) = −(G−1)²/(2G³). Next 1/|z_(k+1)| = 2G³/(G−1)² = (4t+4) + (4G²−2)/(G(G−1)²), so
r_(k+1) = 4t+4, a(k+2) = −(4t+4), and z_(k+2) = 1/G⁴ − 2/G². The hypothesis holds again for G²
with t' = 2t² − 1. Starting from G = ε, t = 199 at k = 4: a(5) = −199, a(6) = −800, and in general
a(2n−1) = −t, a(2n) = −(4t+4) = 4a(2n−1) − 4, a(2n+1) = −(2t² − 1) = −2a(2n−1)² + 1 for n ≥ 3;
all these terms are negative.

**Evidence.**
- Lean (Mathlib): [`A228934_mathlib.lean`](A228934_mathlib.lean), `A228934_main`: with the A228929 algorithm
  defined over ℝ (Mathlib `round`) and x = √44 − 6: a 1 = 2, a 2 = 4, a 3 = 15, a 4 = −99,
  (∀ n ≥ 4, a n < 0), and ∀ n ≥ 3, a (2n) = 4 a (2n−1) − 4 ∧ a (2n+1) = −2 a (2n−1)² + 1.
  Lemmas `A228934_stepA`, `A228934_stepB` (the two-step lemma), `A228934_chain` (G = ε^(2^m)).
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the algorithm in exact Q(√44) arithmetic (signs and rounding at 4000 digits)
  reproduces the 10 OEIS terms, the conjecture for 16 terms, and the invariant z_(4+2m) = 1/G² − 2/G.
- Outside Lean: nothing.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: the entry still states the conjecture and links no proof; web search found
none; not in google-deepmind/formal-conjectures. G. Artico's note for A228931 (linked there) proves the
norm-1-unit lemma for the one-step squaring recurrence; the two-step invariant with denominator 2G³ used here
is not in it (per the 2026-11-04 review of that note).
