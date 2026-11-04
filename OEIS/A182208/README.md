# OEIS A182208: Carmichael numbers divisible by 7 are never 7(6m+1)(6n-1)

**Source.** OEIS [A182208](https://oeis.org/A182208), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 7 can be written in one of two ways: (1) C=7*(6m+1)*(6n+1) ... or (2) C=7*(6m-1)*(6n-1) ... In other words, there aren't Carmichael numbers divisible by 7 of the form C=7*(6m+1)*(6n-1)."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 6 | C - 1; with 7 | C and 7 ≡ 1 (mod 6), C/7 ≡ 1 (mod 6). C/7 is composite (a Carmichael number has at least three prime factors) and prime to 6, and any factorisation C/7 = d e has d e ≡ 1 (mod 6), which forces d ≡ e ≡ 1 or d ≡ e ≡ 5 (mod 6). So both written forms occur as splittings and the mixed form never does.

**Evidence.**
- Lean (Mathlib): [`A182208_mathlib.lean`](A182208_mathlib.lean) proves the full result (`A182208_main, A182208_no_mixed`): a Carmichael number C divisible by 7 is 7de with d, e > 1 and d = e = 1 or d = e = 5 (mod 6), every factorization C = 7de has this form, and 7(6m+1)(6n-1) is never Carmichael; Korselt's necessary direction via Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`, `three_le_card_primeFactors`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182208.lean`](A182208.lean): `cofactor` (C/7 ≡ 1 mod 6, omega) and `split` (d e ≡ 1 mod 6 forces d ≡ e ∈ {1, 5}, residues by decide). Outside Lean: Korselt's criterion (necessary direction),
  which needs Fermat's little theorem and a primitive root mod p.
- `certificate/korselt_residues.py`: scan of Pinch's list of all Carmichael numbers below 10^21
  ([`data/pinch/c21.gz`](../../DATA.md), 57 s). A182208: 1 485 414 Carmichael numbers below 10^21 divisible by 7, C/7 ≡ 1 (mod 6) in every case.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182208_mathlib.lean`](A182208_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182208.lean`](A182208.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Known. The entry itself already resolves it: Greathouse comment (Oct 2012): the conjecture follows from Korselt's criterion ([OEIS A182208](https://oeis.org/A182208), fetched 2026-11-04). Searched: entry, OEIS cross-reference search, edit history. Nothing new for OEIS. (Prior-art review 2026-11-04.)
