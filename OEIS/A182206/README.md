# OEIS A182206: Carmichael numbers divisible by 37 and 73 are 37·73·(18n+91)

**Source.** OEIS [A182206](https://oeis.org/A182206), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 37 and 73 can be written as C = 37*73*(18n+91), where n is natural."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Write C = 2701 m. Korselt gives 36 | C - 1 and 72 | C - 1, so 2701 m ≡ 37 m ≡ 1 (mod 72), i.e. m ≡ 37 (mod 72) (37^2 ≡ 1), hence m ≡ 1 (mod 18). m = 37 would make 37^2 | C, impossible for a Carmichael number, so m ≥ 109 and m = 18n + 91 with n ≥ 1. (Korselt gives the stronger m ≡ 37 mod 72.)

**Evidence.**
- Lean (Mathlib): [`A182206_mathlib.lean`](A182206_mathlib.lean) proves the full result (`A182206_main`): every Carmichael number divisible by 37 and 73 is 37*73*(18n+91) with n >= 1; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd` and squarefreeness. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182206.lean`](A182206.lean): `cofactor`: 2701 m ≡ 1 (mod 72) and 37 ∤ m imply m ≡ 37 (mod 72) and m = 18n + 91 with n ≥ 1 (omega). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182206: 487 511 Carmichael numbers below 10^21 divisible by 37·73, no exception.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182206_mathlib.lean`](A182206_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182206.lean`](A182206.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Known. The entry itself already resolves it: Greathouse comment (Oct 2012): follows from Korselt; more is true, 37*73*(72k+1) ([OEIS A182206](https://oeis.org/A182206), fetched 2026-11-04). Searched: entry, OEIS cross-reference search, edit history. Nothing new for OEIS. (Prior-art review 2026-11-04.)
