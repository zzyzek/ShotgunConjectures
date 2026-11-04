# OEIS A107363: the nonnegative terms are exactly the Fibonacci numbers

**Source.** [A107363](https://oeis.org/A107363) (expansion of (1−x)(1+x)²(1+x²)(1−x²+2x³+x⁴)/((1−x²−x⁴)(1+x²+2x⁴−x⁶+x⁸))),
comment by C. Dement (2005): "Conjectures: { Fib(n) | n in naturals } = { a(n) | n in naturals, a(n) >= 0 } = { a(n) |
n in naturals, n not of the form 6*n+2 } (naturals include 0)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Also a(6j+2) = −L(3j+1) (the entry's A048876 formula, marked "conjecture").

**Argument.** The denominator multiplies out to 1 − 4x⁶ − x¹², and the numerator has degree 9, so
a(n+12) = 4a(n+6) + a(n). Since F(k+6) = 4F(k+3) + F(k) (likewise for Lucas numbers), each 6-section is fixed by
two initial values: a(6j) = F(3j+2), a(6j+1) = a(6j+3) = F(3j+1), a(6j+2) = −L(3j+1) < 0, a(6j+4) = F(3j+3),
a(6j+5) = 0. These cover every F(i) (F(0) = 0 from the last section).

**Evidence.**
- Lean: [`A107363.lean`](A107363.lean): the polynomial products, the 12 initial values from the numerator, the six
  section formulas for all j, and the two set equalities (stated as: a(n) ≥ 0 iff n ≢ 2 mod 6; those terms are
  Fibonacci numbers; every Fibonacci number occurs).
- Lean + Mathlib: [`A107363_mathlib.lean`](A107363_mathlib.lean), `A107363_main`: for every c with
  mk c · den = num in ℤ⟦X⟧ (`PowerSeries`; such c exists, `A107363_gf`): c(n) ≥ 0 iff n ≢ 2 (mod 6),
  {c(n) : c(n) ≥ 0} = {c(n) : n ≢ 2 (mod 6)} = {`Nat.fib` i}, and c(6j+2) = −(F(3j) + F(3j+2)) = −L(3j+1).
  Outside Lean: nothing.
- `certificate/check.py` (scan script): 600 terms.

**Review level.** `lean-proof`: the g.f. statement itself, in [`A107363_mathlib.lean`](A107363_mathlib.lean).
**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). Follows in a few lines from Barker's recurrence and F(k+6)=4F(k+3)+F(k); not stated anywhere found. Sources: [OEIS A107363 (fetched 2026-11-04)](https://oeis.org/A107363): still says Conjectures; Barker's recurrence a(n)=4a(n-6)+a(n-12) is there, no proof. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google: A107363.
