# Guy B2: a harmonic number with two harmonic seeds

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2 (p. 76). n is harmonic if H(n) = n·d(n)/σ(n) is an integer.
Cohen and Sorli call a harmonic number a seed if it has no smaller proper unitary divisor that
is harmonic (other than 1). Goto and Shibata ask, among other questions, whether every
harmonic number has a unique harmonic seed.

**Reading.** "Seed of n" = a harmonic seed that is a unitary divisor of n (a product of some of
the prime powers exactly dividing n). 1 is excluded.

**Result.** No. n = 2⁴·3·5²·7²·19·31²·83·331 = 29495815011600 (H = 525) has two seeds:
m₁ = n/5² = 1179832600464 (H = 217) and m₂ = n/3 = 9831938337200 (H = 350).

**Argument.** Of the 2⁸ unitary divisors of n, exactly three are harmonic and > 1: m₁, m₂, n.
A unitary divisor of m₁ is a unitary divisor of n, and m₂ is not a divisor of m₁; so m₁ has no
smaller harmonic unitary divisor > 1. The same holds for m₂. Hence both are seeds of n.
The scan also found no powerful and no deficient harmonic number > 1 below 10^14 (from the
OEIS A001599 list); that side remark was not rechecked.

**Evidence.**
- Lean (Mathlib): [`B2_7_mathlib.lean`](B2_7_mathlib.lean) proves `B2_7_main`: n is harmonic with H(n) = 525 (σ = Mathlib `ArithmeticFunction.sigma 1`, d = `Nat.divisors` card), m₁ and m₂ are seeds (harmonic, > 1, no harmonic unitary divisor strictly between 1 and themselves) and unitary divisors of n, H = 217 and 350, m₁ ≠ m₂; `B2_7_false` negates uniqueness. σ, d by multiplicativity and the classification of unitary divisors as sub-products of the prime-power factors (new lib module `OpenProblemsLib.ArithFactor`). Outside Lean: nothing (the side remark on powerful/deficient harmonic numbers below 10^14 is not checked).
- Lean: [`B2_7.lean`](B2_7.lean) checks primality of the bases, n's value, H(n) = 525, and
  the harmonic unitary divisors, with σ and d by the product formulas.
  Outside Lean: that σ and d are multiplicative.
- `certificate/harm_check.py` (second reader): factorizations by trial division, H values,
  unitary divisors. The scan's `harm.py`, `harm2.py` are copied (they read the OEIS A001599
  b-file in `../open-problems/scratch/nt-AB/b001599.txt`).

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`B2_7_mathlib.lean`](B2_7_mathlib.lean)).
**Prior art.** Known: Goto & Okeya, [Japan J. Indust. Appl. Math. 24 (2007)](https://projecteuclid.org/journals/japan-journal-of-industrial-and-applied-mathematics/volume-24/issue-3/All-Harmonic-Numbers-Less-than-1014/jjiam/1197909113.full), give this same n = 2⁴·3·5²·7²·19·31²·83·331 with seeds n/5² and n/3 ([Goto's slides](https://web.archive.org/web/2020/https://www.ma.noda.tus.ac.jp/u/tg/files/uts.pdf)). Searched: web, Goto's slides, OEIS A001599/A035527. 2026-11-04.
