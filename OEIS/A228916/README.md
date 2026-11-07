# OEIS A228916: indices of primes in A108300 are 1 and multiples of 3

**Source.** [A228916](https://oeis.org/A228916), indices n with A108300(n) prime, where
[A108300](https://oeis.org/A108300)(n) = 3a(n−1) + a(n−2), a(0) = 1, a(1) = 5. Comment: "Conjecture: for n>1 a(n)
is a multiple of 3." (OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True: if A108300(n) is prime then n = 1 or 3 | n.

**Argument.** A108300 mod 10 is periodic with period 12: 1, 5, 6, 3, 5, 8, 9, 5, 4, 7, 5, 2. For n ≡ 2 (mod 3)
the residue is even, and for n ≡ 1 (mod 3) it is 5. The sequence is increasing with a(2) = 16, so for n ≥ 2 the
term is an even number > 2 or a multiple of 5 larger than 5, hence composite. Only n = 1 (a(1) = 5) and
n ≡ 0 (mod 3) remain.

**Evidence.**
- Lean (Mathlib): [`A228916_mathlib.lean`](A228916_mathlib.lean), `A228916.A228916_main :
  Nat.Prime (a n) → n = 1 ∨ 3 ∣ n` with `a` the A108300 recurrence. Check `tools/leancheck-mathlib.sh`: OK,
  no warnings, axioms propext, Classical.choice, Quot.sound.
- Outside Lean: nothing beyond reading the definition.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones). The argument is a two-line congruence check; no published proof found.
