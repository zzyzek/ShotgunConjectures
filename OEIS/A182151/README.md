# OEIS A182151: Carmichael numbers divisible by 31 lie in three classes mod 2790

**Source.** OEIS [A182151](https://oeis.org/A182151), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 31 can be written in one of the following three forms: C = 2790n+31; C = 2790n+31^2 or C = 2790n+31*61, where n is natural."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 30 | C - 1. With 31 | C, the Chinese remainder theorem gives C ≡ 31 (mod 930). The three lifts of 31 mod 930 to residues mod 2790 are 31, 961 = 31^2 and 1891 = 31·61.

**Evidence.**
- Lean (Mathlib): [`A182151_mathlib.lean`](A182151_mathlib.lean) proves the full result (`A182151_main`): every Carmichael number divisible by 31 is 2790n + 31, 2790n + 961 or 2790n + 1891; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182151.lean`](A182151.lean): `residues`: C ≡ 0 (mod 31) and C ≡ 1 (mod 30) imply C mod 2790 ∈ {31, 961, 1891} (omega). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182151: 3 570 658 Carmichael numbers below 10^21 divisible by 31, no exception.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182151_mathlib.lean`](A182151_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182151.lean`](A182151.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Known. The entry itself already resolves it: Greathouse comment (Oct 2012): numbers are 31 mod 930, so the conjecture is true ([OEIS A182151](https://oeis.org/A182151), fetched 2026-11-04). Searched: entry, OEIS cross-reference search, edit history. Nothing new for OEIS. (Prior-art review 2026-11-04.)
