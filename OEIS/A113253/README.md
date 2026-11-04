# OEIS A113253: a(m, 2n+1) is a perfect square (m = 7)

**Source.** [A113253](https://oeis.org/A113253) (m = 7 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².


**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

**Evidence.**
- Lean: [`A113253.lean`](A113253.lean) proves, for every m : Int, both recurrences (by unfolding and `grind`), the four
  initial identities, and a(m, 2n+1) = y(m, n)² for all n; it also checks that a(7, 0..9) is the entry's data.
  Axioms: propext, Classical.choice, Quot.sound. Nothing outside Lean.
- `certificate/check.py`: m = 0..12, n < 300 in exact integers; `certificate/symbolic_check.py` (scan script): sympy over Z[m].

**Review level.** `lean-proof`.
**Prior art.** Verdict partly-known (OEIS status conjecture; searched 2026-11-04). The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture. Sources: [OEIS A113253 (fetched 2026-11-04)](https://oeis.org/A113253): still says Conjecture (family for all m); [Robert Israel, comment in OEIS A113249 (Oct 2017)](https://oeis.org/A113249): proves the m = 3 case: a(2n+1) = b(n)^2, b(n) = Re((2+sqrt(-5))^(n+1)); [Ralf Stephan, comment in OEIS A113254 (May 2026)](https://oeis.org/A113254): m = 8 case proved by an autonomous AI agent (Lean file linked there); [Eric Simon Jacob, formulas in OEIS A097948, A113249, A113251, A113253 (2023)](https://oeis.org/A113251): closed form m^(n+1)(1-(-1)^n+2cos((n+1)arccos(-2/m)))/4 for m = 1, 3, 5, 7; at odd n it is a square by the half-angle identity, which nobody states. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS sister entries A113254, A097948, A056450; Google: A113249 perfect square family.
