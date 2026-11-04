# OEIS A182532: Carmichael numbers divisible by 7 and 17: the four residue classes mod 120

**Source.** OEIS [A182532](https://oeis.org/A182532), conjecture by Marius Coman (2012): Conjectures (1)-(4): a Carmichael number C divisible by 7 and 17 "of the form 10k+1 can be written as C = 7*17*(120n+119)"; of the form 10k+5 as 7*17*(120n+95); 10k+3 as 7*17*(120n+47); 10k+9 as 7*17*(120n+71).
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 6 | C - 1 and 16 | C - 1, so 48 | C - 1. With C = 119 m and 119 ≡ 23 (mod 48), m ≡ 23^(-1) = 23 (mod 48). C ≡ 9m (mod 10) fixes m mod 5 from C mod 10, and m ≡ 23 (mod 48) gives m ≡ 7 (mod 8), m ≡ 2 (mod 3); together m mod 120 is 119, 95, 47, 71 in the four cases.

**Evidence.**
- Lean (Mathlib): [`A182532_mathlib.lean`](A182532_mathlib.lean) proves the full result (`A182532_main`): the four residue-class implications for Carmichael numbers divisible by 7 and 17; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182532.lean`](A182532.lean): `c1`, `c5`, `c3`, `c9`: the four implications (omega). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182532: 254 553 Carmichael numbers below 10^21 divisible by 7·17, no exception in any of the four classes.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182532_mathlib.lean`](A182532_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182532.lean`](A182532.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** New to OEIS, but immediate from Korselt's criterion. [OEIS A182532](https://oeis.org/A182532) (fetched 2026-11-04) still states Conjectures (1)-(4) with no proof; no pending edit in the history. Unlike the sister Carmichael entries, no Korselt note was added in 2012. Worth an OEIS comment. (Prior-art review 2026-11-04.)
