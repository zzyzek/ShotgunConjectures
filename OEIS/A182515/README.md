# OEIS A182515: Carmichael numbers divisible by 23 and 67 are 23·67·(66n+23)

**Source.** OEIS [A182515](https://oeis.org/A182515), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 23 and 67 can be written as C = 23*67*(66n+23)."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 22 | C - 1 and 66 | C - 1. With C = 1541 m and 1541 ≡ 23 (mod 66), 23 m ≡ 1 (mod 66), so m ≡ 23 (mod 66) because 23^2 = 529 ≡ 1. (m = 23 gives 23^2 | C, so n ≥ 1.)

**Evidence.**
- Lean (Mathlib): [`A182515_mathlib.lean`](A182515_mathlib.lean) proves the full result (`A182515_main`): every Carmichael number divisible by 23 and 67 is 23*67*(66n+23) with n >= 1; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd` and squarefreeness. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182515.lean`](A182515.lean): `cofactor`: 1541 m ≡ 1 (mod 66) implies m ≡ 23 (mod 66) (omega). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182515: 286 744 Carmichael numbers below 10^21 divisible by 23·67, no exception.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182515_mathlib.lean`](A182515_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182515.lean`](A182515.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Known. The entry itself already resolves it: Greathouse comment (Oct 2012): follows from Korselt, 67 | a(n) so a(n) = 1 mod 66 ([OEIS A182515](https://oeis.org/A182515), fetched 2026-11-04). Searched: entry, OEIS cross-reference search, edit history. Nothing new for OEIS. (Prior-art review 2026-11-04.)
