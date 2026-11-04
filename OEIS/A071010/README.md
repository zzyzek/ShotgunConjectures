# OEIS A071010: if n is not a sum of two squares then 4 | sigma(n)

**Source.** [A071010](https://oeis.org/A071010) (sigma(k)/4 for k not a sum of 2 squares), comment:
"Conjecture : if n is not the sum of 2 squares sigma(n) == 0 (mod 4) ..." (OEIS text, CC BY-SA 4.0.)
The same statement is B. Cloitre's 2002 conjecture in [A022544](https://oeis.org/A022544).

**Result.** True. Proved in A022544 by M.-A. Leduc (Mar 2026); re-derived here.

**Argument.** By the two-squares theorem, n is not a sum of two squares iff some prime p ≡ 3 (mod 4)
divides n to an odd power e. Then σ(p^e) = (1 + p) + p^2(1 + p) + … + p^(e−1)(1 + p) ≡ 0 (mod 4), since
4 | p + 1, and σ is multiplicative.

**Evidence.**
- `certificate/check.py`: n < 10^6.
- Lean (Mathlib): [`A071010_mathlib.lean`](A071010_mathlib.lean), theorem `A071010_conjecture`: if n is not x² + y²
  then 4 ∣ σ(n) (`Nat.eq_sq_add_sq_iff`, `isMultiplicative_sigma`). Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** Proof in OEIS A022544 (M.-A. Leduc, Mar 11 2026); A071010 still says "Conjecture" (checked 2026-11-01).
Resolved by others.
