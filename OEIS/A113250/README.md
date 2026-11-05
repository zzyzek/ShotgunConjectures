# OEIS A113250: a(m, 2n+1) is a perfect square (m = 4)

**Source.** [A113250](https://oeis.org/A113250) (m = 4 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².


**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

**Evidence.**
- Lean: [`A113250.lean`](A113250.lean) proves, for every m : Int, both recurrences (by unfolding and `grind`), the four
  initial identities, and a(m, 2n+1) = y(m, n)² for all n; it also checks that a(4, 0..9) is the entry's data.
  Axioms: propext, Classical.choice, Quot.sound. Nothing outside Lean.
- `certificate/check.py`: m = 0..12, n < 300 in exact integers; `certificate/symbolic_check.py` (scan script): sympy over Z[m].

**Review level.** `lean-proof`.
**Prior art.** Known (corrected 2026-11-05). The whole A113249 family (every m) was already proved in Lean 4 by others: [KitaKen1/oeis-a113249-family-square-terms-lean](https://github.com/KitaKen1/oeis-a113249-family-square-terms-lean/blob/9b999db08344184285e8050c2722c845fd5f5309/lean/OeisA113249FamilyFC.lean), marked solved in google-deepmind/formal-conjectures (PR #4963, 2026-08-15). This project's proof is independent. Earlier partial results: m = 3 (Israel 2017), m = 8 (Stephan 2026). The OEIS entry still says Conjecture. The 2026-11-04 review did not search formal-conjectures.
