# Guy B2: H(n) = 3p does not force a harmonic number to be arithmetic

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B2 (p. 76). Goto and Shibata note that every harmonic number n with
H(n) = 3p < 300 (p prime) is arithmetic (d(n) | σ(n)), and ask whether this holds for all
primes p.

**Result.** No. n = 2⁸·7·19²·37·73·113·127 = 25075635936512 has H(n) = 339 = 3·113 and
σ(n) ≡ 288 (mod d(n)). A second example: n = 2⁸·5²·7·19·31·37·73·179 = 12757657068800,
H(n) = 537 = 3·179, σ(n) ≡ 576 (mod d(n)).

**Argument.** Direct computation from the factorizations. (Equivalently, by Goto–Shibata,
a harmonic n is arithmetic iff H(n) | n; here 3 ∤ n, so 3p ∤ n.)

**Evidence.**
- Lean (Mathlib): [`B2_8_mathlib.lean`](B2_8_mathlib.lean) proves `B2_8_main`: both n are harmonic with H(n) = 3·113 resp. 3·179 (primes) and not arithmetic, σ(n) mod d(n) = 288 resp. 576 (σ = Mathlib `ArithmeticFunction.sigma 1`, d = `Nat.divisors` card, computed by multiplicativity, `OpenProblemsLib.ArithFactor`); `B2_8_false` negates the question. Outside Lean: nothing.
- Lean: [`B2_8.lean`](B2_8.lean) checks values, primality of all bases and of p, H(n) = 3p
  and σ(n) mod d(n) ≠ 0, with σ, d by product formulas. Outside Lean: multiplicativity.
- `certificate/harm_check.py` (second reader). Scan scripts `harm.py`, `harm2.py` copied.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`B2_8_mathlib.lean`](B2_8_mathlib.lean)).
**Prior art.** Not found stated. Both examples lie inside the published Goto–Okeya lists (all harmonic n < 10^14 and all with H(n) ≤ 1200), but no source seen remarks on the H(n) = 3p question; the paper body itself was not read. Searched: web, [Goto's slides](https://web.archive.org/web/2020/https://www.ma.noda.tus.ac.jp/u/tg/files/uts.pdf), OEIS A001599 and number searches. 2026-11-04.
