# Coman C101: p(p+2) + 1729 for twin primes: prime factors 2, 3 and 1, 7, 13, 19 mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 101. Paraphrase: For twin primes p, p + 2, the number p(p+2) + 1729 has only the prime factors 2, 3 and primes = 1, 7, 13, 19 (mod 30).

**Result.** True.

**Argument.** For p > 3, p = 6j - 1 and p(p+2) + 1729 = 36(j^2 + 48). A prime r > 3 dividing j^2 + 48 = j^2 + 3*4^2 has
-3 a quadratic residue, so r = 1 (mod 3); r = 5 never divides j^2 + 48 (squares mod 5 are 0, 1, 4). The
primes = 1 (mod 6) prime to 5 are exactly 1, 7, 13, 19 (mod 30). p = 3: 1744 = 2^4 * 109, 109 = 19 (mod 30).
Checked numerically for p < 2e5.

**Evidence.**
- Lean: [`C101.lean`](C101.lean) checks the identity, 5 never divides j^2 + 48, the case p = 3. Core Lean, no Mathlib, no `native_decide`.
- Lean (Mathlib): [`C101_mathlib.lean`](C101_mathlib.lean) proves the full statement, `C101_main`: for primes p, p + 2 every prime factor r of p(p + 2) + 1729 is 2, 3 or = 1, 7, 13, 19 (mod 30). The step r = 1 (mod 3) is done without reciprocity: w = (j - 4)/8 has w^3 = 1, w != 1 in ZMod r, and Fermat's little theorem gives 3 | r - 1.
- Outside Lean: none.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): twin primes below 2e5; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C101_mathlib.lean`](C101_mathlib.lean)); the core-Lean file checks the parts named under Evidence.

**Prior art.** Verdict `new` (immediate). Quadratic reciprocity for j^2 + 3*16; not found stated. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
