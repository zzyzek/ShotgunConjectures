# Coman C023: pq psp base p+1 when q^2 = 2p - 1: fails at (5, 3)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 23. Paraphrase: If p, q are prime and q^2 = 2p - 1, then pq is a Fermat pseudoprime to base p + 1.

**Result.** False: (p, q) = (5, 3) gives 15 and 6^14 = 6 (mod 15). True for every other pair.

**Argument.** Modulo p the base is 1. Modulo q: pq - 1 = p(q-1) + (p - 1) and p - 1 = (q-1)(q+1)/2, so q - 1 | pq - 1
and Fermat gives (p+1)^(pq-1) = 1 provided q does not divide p + 1 = (q^2 + 3)/2, i.e. q != 3.
For q = 3, p = 5: gcd(6, 15) = 3 and 6^k = 6 (mod 15).

**Evidence.**
- Lean: [`C023.lean`](C023.lean) checks the counterexample (hypotheses and 6^14 mod 15 = 6). Core Lean, no Mathlib, no `native_decide`.
- Lean + Mathlib: [`C023_mathlib.lean`](C023_mathlib.lean), `C023_main`: (5, 3) satisfies the hypotheses and
  15 is not a base-6 `Nat.FermatPsp`, and for all other primes p, q with q^2 = 2p - 1, `Nat.FermatPsp (p * q) (p + 1)`
  (Fermat's little theorem from Mathlib). Outside Lean: nothing.
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): all pairs with q < 3000; output in `certificate/check.log`.

**Second reader: disputed.** The scan reports 'proved'; (p, q) = (5, 3) satisfies the hypotheses and 15 is not a base-6 psp (6^14 mod 15 = 6). True for q > 3.

**Review level.** `lean-proof`: the full result (counterexample and the q > 3 part) is proved in [`C023_mathlib.lean`](C023_mathlib.lean) (axioms propext, Classical.choice, Quot.sound); the core file checks the counterexample.

**Prior art.** Verdict `new` (immediate). Direct computation. Sources: none found. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement (2026-11-04).
