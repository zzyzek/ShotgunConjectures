# OEIS A182381: Carmichael numbers divisible by 17 and 29 are 952n + 561

**Source.** OEIS [A182381](https://oeis.org/A182381), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 17 and 29 can be written as C = 952*n + 561."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 16 | C - 1 and 28 | C - 1, so C ≡ 1 (mod 112), in particular C ≡ 1 (mod 56). With 17 | C and 952 = 56·17, the Chinese remainder theorem gives one class mod 952, which is 561 = 33·17 (561 ≡ 1 mod 56).

**Evidence.**
- Lean (Mathlib): [`A182381_mathlib.lean`](A182381_mathlib.lean) proves the full result (`A182381_main`): every Carmichael number divisible by 17 and 29 is 952n + 561; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182381.lean`](A182381.lean): `residue`: C ≡ 0 (mod 493) and C ≡ 1 (mod 112) imply C ≡ 561 (mod 952) (omega). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182381: 481 455 Carmichael numbers below 10^21 divisible by 17·29, no exception.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182381_mathlib.lean`](A182381_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182381.lean`](A182381.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Known. The entry itself already resolves it: Greathouse comment (Oct 2012): follows from Korselt; more is true, 2465 mod 55216 ([OEIS A182381](https://oeis.org/A182381), fetched 2026-11-04). Searched: entry, OEIS cross-reference search, edit history. Nothing new for OEIS. (Prior-art review 2026-11-04.)
