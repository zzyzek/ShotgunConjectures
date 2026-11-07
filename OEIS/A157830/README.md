# OEIS A157830: the "higher invariant than E8" conjecture is not a statement; its check is trivial

**Source.** OEIS [A157830](https://oeis.org/A157830) (Bagula, Adamson 2009), expansion of 1/p(x),
p(x) = 1 + 759x^8 + 2576x^12 + 759x^16 + x^24 (binary Golay code weight enumerator). Old comment:
"Conjecture: An higher symmetry elliptical Invariant than E8 exists … s[1/x]=s[x] which checks in
Mathematica", s = p^3/(q1^3 q2^3), q1 = 24 + 440x^3 + 264x^6 + x^12, q2 = 1 + 264x^6 + 440x^9 + 24x^12.
Removed by Joerg Arndt, 2022-12-19 (who noted the entry is A001920 with zeros interspersed).

**Result.** Misstated. "A higher symmetry elliptical invariant than E8 exists" has no defined
meaning. The concrete check s(1/x) = s(x) holds, for a trivial reason: p is palindromic of degree 24
and q2 is the reversal of q1.

**Evidence.** Lean (Mathlib): [`A157830_mathlib.lean`](A157830_mathlib.lean), `A157830_main`
(s(x⁻¹) = s(x), x ≠ 0, any field). Axioms propext, Classical.choice, Quot.sound. Outside Lean: the
judgement that the first sentence has no mathematical content.

**Review level.** `lean-proof` (identity).

**Prior art.** Entry history (2026-11-07). Not in formal-conjectures or oeis-lean-proofs.
