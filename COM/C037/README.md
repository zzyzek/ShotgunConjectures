# Coman C037: Infinitely many Poulet numbers (n+1)p^2 - np with p Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 37. Paraphrase: There are infinitely many Poulet numbers (n+1)p^2 - np, n >= 1, with p a Poulet number.

**Result.** True (via Larsen 2025).

**Argument.** (n+1)561^2 - 561n = 561 + 314160(n + 1), so the Poulet numbers of this shape with p = 561 are exactly
those N = 561 (mod 314160 = 561 * 560) with N > 561^2. The progression contains the Carmichael number 561
(and is Carmichael compatible: g = 561, lambda(561) = 80 | 560), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many
Carmichael numbers, all Poulet. Below 1e13: 10054063041, 709277461761, 795066389601, 7650392590401.

**Evidence.**
- Lean: [`C037.lean`](C037.lean) checks 561 Carmichael (all bases) and the identity. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: Larsen's theorem.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): compatibility and examples below 1e13; output in `certificate/check.log`.

**Review level.** `lean-witness`: the finite facts are checked in core Lean; the steps named under Evidence are outside Lean.

**Prior art.** Verdict `new` (immediate). Follows directly from Larsen 2025 (the progression 561 mod 314160 is Carmichael compatible and contains 561); nobody has noted this, and A215343 still lists it as a conjecture. Sources: [OEIS A215343 (fetched 2026-11-04)](https://oeis.org/A215343): still states this conjecture; no proof; [D. Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025)](https://arxiv.org/abs/2504.09056): every Carmichael-compatible progression has infinitely many Carmichael numbers; does not mention Coman. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A215343, Google: Larsen 2025 Carmichael progressions Coman (2026-11-04).
