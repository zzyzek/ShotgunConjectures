# OEIS A008676: coefficients of 1/((1-x^3)(1-x^5)) as a floor formula

**Source.** [A008676](https://oeis.org/A008676), comment by J. W. Layman (2009):
"Conjecture: a(n) = Floor(2*(n + 3)/3) - Floor(3*(n + 3)/5)." (OEIS text, CC BY-SA 4.0.)

**Result.** True for all n ≥ 0.

**Argument.** Multiplying out, (1 − x^3 − x^5 + x^8)·A(x) = 1, so a(n) = a(n−3) + a(n−5) − a(n−8) for
n ≥ 8 with a(0..7) = 1, 0, 0, 1, 0, 1, 1, 0. The floor formula R(n) satisfies the same recurrence
(R(n+15) = R(n) + 1 and the recurrence holds on each residue class mod 15) and matches the 8 initial values.

**Evidence.**
- Lean: [`A008676.lean`](A008676.lean) defines a(n) by the recurrence above, proves that R satisfies it
  (`omega`, one case per n mod 15) and proves a(n) = R(n) for all n. Axioms: propext, Quot.sound.
- Lean + Mathlib: [`A008676_mathlib.lean`](A008676_mathlib.lean), `A008676_main`: in ℤ⟦X⟧ (`PowerSeries`),
  mk R · (1 − X^3)(1 − X^5) = 1 with R(n) = ⌊2(n+3)/3⌋ − ⌊3(n+3)/5⌋, and every A with A(1 − X^3)(1 − X^5) = 1
  has coefficients R(n). Outside Lean: nothing.
- `certificate/check.py`: n < 3000 directly from the g.f.

**Review level.** `lean-proof`: the g.f. statement itself, in [`A008676_mathlib.lean`](A008676_mathlib.lean).
**Prior art.** Partly known. [A008676](https://oeis.org/A008676) already lists a(n) = floor((2n+5)/5) - floor((n+2)/3) (T. Akinari, 2013, without proof), which equals Layman's formula by elementary floor identities; Layman's version is still marked "Conjecture". Searched OEIS entry, references and history. Checked 2026-11-04.
