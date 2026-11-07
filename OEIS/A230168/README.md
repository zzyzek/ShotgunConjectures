# OEIS A230168: every prime 45·2^n − 1 ends in 9

**Source.** OEIS [A230168](https://oeis.org/A230168), primes of the form 45·2^n − 1. Comment:
"Conjecture: each term in the sequence ends with digit 9." (OEIS text, CC BY-SA 4.0.)

**Result.** True, and already answered in the entry: Alonso del Arte (Oct 11 2013) notes that every
term is ≡ 89 (mod 90), hence ends in 9.

**Argument.** n = 0 gives 44, not prime. For n ≥ 1, 45·2^n = 10·(9·2^(n−1)), so 45·2^n − 1 ≡ 9 (mod 10).

**Evidence.**
- Lean (Mathlib): [`A230168_mathlib.lean`](A230168_mathlib.lean). `A230168_main`: if p is prime and
  p = 45·2^n − 1 for some n, then p % 10 = 9. Axioms propext, Classical.choice, Quot.sound; zero warnings.
- [`certificate/check.gp`](certificate/check.gp): the probable primes 45·2^n − 1 with n ≤ 2000 all end in 9.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry itself contains the proof (del Arte, 2013). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (no A230168 file found).
