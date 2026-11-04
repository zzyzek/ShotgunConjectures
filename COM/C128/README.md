# Coman C128: (P + 5^m)/10 is composite for every m, for infinitely many Poulet P with 15 | P

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 128. Paraphrase: Every Poulet number P divisible by 15 has m >= 1 with (P + 5^m)/10 prime.

**Result.** False (non-constructive): every odd P = 27334771482791460 (mod 76580312516934135) makes (P + 5^m)/10 composite for all m >= 1, and this progression contains infinitely many Carmichael numbers.

**Argument.** Covering: q | P + 5^m on the class m = r (mod ord_q(5)) for (q, ord, r) = (7, 6, 1), (13, 4, 0), (19, 9, 2),
(31, 3, 0), (37, 36, 26), (601, 12, 10), (829, 9, 5), (5167, 18, 17); the classes cover Z/36. The progression is
Carmichael compatible (gcd 15, lambda(15) = 4, h = gcd(4, M) = 1, M odd), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many
Carmichael numbers; they are Poulet numbers divisible by 15. No explicit P is known.

**Evidence.**
- Lean: [`C128.lean`](C128.lean) checks the covering for every odd P in the progression and every m >= 1 (q divides (P + 5^m)/10 and 1 < q < (P + 5^m)/10). Core Lean, no Mathlib, no `native_decide`.
- Outside Lean: Larsen's theorem.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): covering data and compatibility; output in `certificate/check.log`.

**Review level.** `lean-witness`: the finite facts are checked in core Lean; the steps named under Evidence are outside Lean.

**Prior art.** Verdict `partly-known`. Method is Erdos-type covering plus Larsen 2025 for Carmichael numbers in the progression; this progression and the answer were not found stated. Sources: [P. Erdos, On integers of the form 2^k + p and some related problems, Summa Brasil. Math. 2 (1950) 113-123; construction as in C. Pomerance, covering-congruence talk slides](https://math.dartmouth.edu/~carlp/PDF/covertalkunder.pdf): covering congruences give residue classes of odd k with k + 2^n composite for all n; not for 5p with p prime; [D. Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025)](https://arxiv.org/abs/2504.09056): every Carmichael-compatible progression has infinitely many Carmichael numbers; does not mention Coman. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, Google: covering congruences 5^m Poulet, Google: Coman (P+5^m)/10 (2026-11-04).
