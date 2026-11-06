# OEIS A202943: a(n) is odd iff n has no 1-bit at an even position ≥ 2

**Source.** [A202943](https://oeis.org/A202943) (Paul D. Hanna), "G.f.: [ Sum_{n>=0} (n+1)*(n+2)/2 *
2^(n*(n-1)) * x^n ]^(1/3)." Comment: "Conjecture: the characteristic function of a(n) (mod 2) equals
(1+x)*(1+x^2)*(1+x^8) * Sum_{n>0} x^(32*A000695(n)), where A000695 is the sums of distinct powers of 4."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** The sum over A000695 must include A000695(0) = 0 (the entry's own example starts 1 + x^32 + ...).
The exponents of the product are n = e + 32m with e ∈ {0,1,2,3,8,9,10,11} and m with base-4 digits in {0,1};
equivalently n has no 1-bit at positions 2, 4, 6, ....

**Result.** True.

**Argument.** Let B(x) = Σ C(n+2,2) 2^{n(n−1)} x^n and A = B^{1/3}.
1. *Integrality.* 2^{n(n−1)} ≡ 1 (mod 9) unless n ≡ 2 (mod 3), and then 3 | C(n+2,2) and 3 | 2^{n(n−1)} − 1;
   so B ≡ (1−x)^{−3} (mod 9), B(1−x)^3 = 1 + 9D with D ∈ ℤ[[x]], and A = (1−x)^{−1}(1+9D)^{1/3} has integer
   coefficients (the binomial coefficients C(1/3, k)·9^k are integers). It also gives a(n) ≡ 1 (mod 3), the
   entry's formula.
2. *Parity.* Mod 2, B ≡ 1 + x, so A^4 ≡ A(1+x). In characteristic 2, [x^n] f² = f_{n/2} for even n and 0 for odd
   n, so [x^n] A^4 = a(n/4) if 4 | n and 0 otherwise. Hence a(n) ≡ a(n−1) + [4|n]·a(n/4), a(0) = 1. The
   indicator s(n) = t(⌊n/4⌋), t(m) = [m has no 1-bit at an even position], satisfies the same recursion
   (case split on n mod 4 and on ⌊n/4⌋ mod 4), so a(n) ≡ s(n). Finally s(n) = 1 iff n = e + 32m as above.
   (Equivalently A ≡ (1+x)^{1/3} = (1+x)(1+x²)(1+x⁸)(1+x^{32})(1+x^{128})··· mod 2, from the binary expansion
   1/3 = 1 + 2 + 2³ + 2⁵ + ··· in ℤ₂.)

**Evidence.**
- Lean (Mathlib): [`A202943_mathlib.lean`](A202943_mathlib.lean). `A202943_main`: if Aq ∈ ℚ⟦X⟧ has Aq³ = B and
  constant term 1 (the entry's definition), then every coefficient is an integer z with `Odd z ↔ charSet n`
  (charSet = exponents of the conjectured product). Ingredients: `Aint_cube` (an integer cube root, built
  coefficient by coefficient; exact division by 3 from `b_mod9` and `cube_mod9`/`coeff_G3`), `cube_root_unique`,
  `A202943_conjecture`, `coeff_sq`, `parity`, `charSet_iff`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): exact cube root for n ≤ 200: integral, ≡ 1 mod 3, parity
  pattern holds; b-file (n ≤ 50) agrees.
- Outside Lean: the reading of A000695 as base-4 digits 0/1. (In Lean, integrality uses the mod-9 induction
  form of step 1 rather than the binomial series.)

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture; no proof found by web search. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06). The argument is
the standard Frobenius computation of (1+x)^{1/3} in GF(2)[[x]]; immediate once B ≡ 1 + x (mod 2) is noticed.
