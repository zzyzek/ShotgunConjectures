# Coman C076: Infinitely many Poulet numbers divisible by 15 with SCD1 beginning 2, 4, 7

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 76. Paraphrase: There are infinitely many Poulet numbers divisible by 15 whose set of Smarandache-Coman divisors of order 1 is {2, 4, 7, n1, ..., ni} with i > 0.

**Reading.** SCD1(n) = (S(d1 - 1), ..., S(dm - 1)) over the prime factors d1 < ... < dm, S the Kempner (Smarandache) function, listed in factor order (Coman's definition, Part two, article 24).

**Result.** True (via Larsen 2025).

**Argument.** Members of the progression 342075735 (mod 3234846615 = 435 * 7 * 11 * 13 * 17 * 19 * 23) are divisible by 3, 5 and the third prime, and = 1 modulo every
prime in between, so (being odd when Carmichael) their three least prime factors are 3, 5 and that prime;
S(2) = 2, S(4) = 4, S(28) = 7. A Carmichael number has at least three prime factors and 3*5*p alone is not in the progression,
so i > 0. The progression is Carmichael compatible in Larsen's sense (g = gcd, h = gcd(lambda(g), M) divides
a - 1, 36 does not divide M), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many Carmichael numbers.

**Evidence.**
- Lean: [`C076.lean`](C076.lean) checks the residues of the progression and the three Kempner values. Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: Larsen's theorem.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): compatibility criterion (Larsen's definition) and residues; output in `certificate/check.log`.

**Review level.** `lean-witness`: the finite facts are checked in core Lean; the steps named under Evidence are outside Lean.

**Prior art.** Verdict `new` (immediate). Follows from Larsen 2025 applied to an explicit progression; not found stated. Sources: [D. Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025)](https://arxiv.org/abs/2504.09056): every Carmichael-compatible progression has infinitely many Carmichael numbers; does not mention Coman. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, Google: Larsen 2025 Coman (2026-11-04).
