# OEIS A004050 / A085634: only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A004050](https://oeis.org/A004050) (line 46):
"Conjecture: Only 5, 11, 17, 35, and 259 can be expressed in two different ways. See A085634."
(OEIS text, CC BY-SA 4.0.) [A085634](https://oeis.org/A085634) (checked 2026-11-01) lists these five
terms with "No more terms < 10^4000" (D. Wasserman, 2005) and no proof.

**Result.** True, given Ellison's 1971 bound on |2^x − 3^y|.

**Argument.** Let 2^a + 3^b = 2^c + 3^d with a > c. Then d > b and
2^c(2^f − 1) = 3^b(3^e − 1) with f = a − c ≥ 1, e = d − b ≥ 1. So 2^c is the exact power of 2 in
3^e − 1 and 3^b the exact power of 3 in 2^f − 1. Lifting the exponent: v_2(3^e − 1) is 1 (e odd) or
2 + v_2(e) (e even), so 2^c ≤ 4e; v_3(2^f − 1) is 0 (f odd) or 1 + v_3(f) (f even), so 3^b ≤ 3f.
From 3^d − 3^b = 2^a − 2^c < 2^a and 3^d − 3^b ≥ (2/3)·3^d we get d ≤ a, so e, f ≤ a. The equation
gives |2^a − 3^d| = |2^c − 3^b| ≤ max(2^c, 3^b) ≤ 4a.
Ellison (1971): |2^x − 3^y| > 2^x e^(−x/10) for x ≥ 12, x ∉ {13, 14, 16, 19, 27}. Since
2^x e^(−x/10) > 4x for x ≥ 12, this forces a ≤ 27. For a ≤ 27, d ≤ a, the only pairs with
|2^a − 3^d| ≤ 4a have a ≤ 8 (16 pairs), and enumerating b < d, c < a over them leaves exactly the
five values.

**Evidence.**
- Lean (Mathlib): [`A004050_mathlib.lean`](A004050_mathlib.lean) proves `A004050_reduction` unconditionally (2^a + 3^b = 2^c + 3^d with c < a gives b < d ≤ a and |2^a − 3^d| ≤ 4a, by lifting the exponent with Mathlib's `padicValNat.pow_two_sub_pow` / `pow_sub_pow`), and `A004050_main`: assuming Ellison's bound (hypothesis `EllisonBound`, stated over ℝ as quoted above), v has two representations iff v ∈ {5, 11, 17, 35, 259} (Ellison forces a ≤ 27, then a kernel enumeration). Outside Lean: Ellison's bound only.
- Lean: [`A004050.lean`](A004050.lean) (`decide`): the 16 pairs, the enumeration over them, and the
  two representations of each value. Outside Lean: the valuation reduction above, and Ellison's bound.
- `certificate/check.py`: the valuation bounds for e, f ≤ 2000, the pair list for X ≤ 60, and a full
  enumeration for a ≤ 27; `certificate/scan_check.py` is the scan's original enumeration.

**Review level.** `lean-witness`: everything except Ellison's bound is proved in Lean + Mathlib ([`A004050_mathlib.lean`](A004050_mathlib.lean)); the main theorem takes Ellison's bound as a hypothesis.
**Prior art.** Partly known. Writing 2^a + 3^b = 2^c + 3^d as 3^d - 2^a = 3^b - 2^c makes it Pillai's equation: Stroeker and Tijdeman (1982), and in the form used here M. A. Bennett, [Pillai's conjecture revisited](https://personal.math.ubc.ca/~bennett/B-Pillai.pdf), J. Number Theory 98 (2003), Thm 1.1, list every c with two solutions of |3^x - 2^y| = c in positive x, y. With the same sign on both sides this leaves 11, 35, 259; exponent 0 gives 5 and 17 by an elementary check. No source states the A085634 conclusion. [A085634](https://oeis.org/A085634) and [A004050](https://oeis.org/A004050) still say only "No more terms < 10^4000". Searched OEIS entries, references and history, web, Bennett 2003. Checked 2026-11-04.
