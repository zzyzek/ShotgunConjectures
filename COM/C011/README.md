# Coman C011: No 3-Carmichael (6x+1)(6y+1)(6z-1): true part and false part

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 11. Paraphrase: No Carmichael number with three prime factors has the shape (6x+1)(6y+1)(6z-1); all are (+,+,+), (-,-,-) or (+,-,-) modulo 6.

**Result.** Misstated. The 'no (+,+,-)' part is true and short; the 'all are of these shapes' part fails for 561 = 3 * 11 * 17.

**Argument.** A prime factor p = 1 (mod 6) gives 6 | p - 1 | C - 1 (Korselt), so C = 1 (mod 6), while
(6x+1)(6y+1)(6z-1) = 5 (mod 6). The factor 3 of 561 is neither 1 nor 5 mod 6. Below 1e10 the 3-Carmichael
numbers have factor patterns (1,1,1), (1,5,5), (5,5,5) and only 561 has (3,5,5).

**Evidence.**
- Lean (Mathlib): [`C011_mathlib.lean`](C011_mathlib.lean) proves the full result (`C011_no_ppm, C011_561`): (6x+1)(6y+1)(6z-1) is never Carmichael when 6x+1 is prime (Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`), and 561 = 3*11*17 is Carmichael and not a product of three numbers = +-1 (mod 6). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C011.lean`](C011.lean) checks the residue computation, the deduction C = 1 (mod 6) from p - 1 | C - 1, and 561 Carmichael by checking all bases. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's necessary condition (p | C Carmichael implies p - 1 | C - 1; needs a primitive root mod p) (first part only).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): pattern count below 1e10; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C011_mathlib.lean`](C011_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C011.lean`](C011.lean) checks the parts named under Evidence.

**Prior art.** Verdict `partly-known` (immediate). The '(+,+,-) impossible' part is the Korselt argument Greathouse cites for the 7-divisible case in A182208; the failure of 'all are of these shapes' at 561 (factor 3) is not stated there (A182208 excludes multiples of 3). Sources: [OEIS A182208 (fetched 2026-11-04)](https://oeis.org/A182208): Coman's observation that no 3-Carmichael (6x+1)(6y+1)(6z-1) exists (restricted to C not divisible by 3); Greathouse 2012 notes the companion 7-divisible conjecture follows from Korselt. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A182208 (2026-11-04).
