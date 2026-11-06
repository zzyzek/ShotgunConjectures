# OEIS A079128: gcd(a(n), n) = 1 for permutations with relatively prime cycle lengths

**Source.** OEIS [A079128](https://oeis.org/A079128) (Vladeta Jovovic and Vladimir Baltic, Dec 27 2002): number of
degree-n permutations with (mutually) relatively prime cycle lengths. Conjecture (Jovovic, Jan 25 2003):
gcd(a(n), n) = 1. The entry now records (Ahaan Kallat, Oct 30 2026) that this and the divisibility by n^2 - 1 are
proved in A. Kallat, "A p-adic Valuation Calculus for Permutations with Restricted Cycle Lengths",
arXiv:2610.40342 (2026), Corollary 6.2. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** "Relatively prime cycle lengths": the gcd of all cycle lengths, fixed points included, is 1
(reproduces the data, certificate/check.py).

**Result.** True; more precisely a(n) = (-1)^(m+1) (mod p) for each prime p dividing n, n = pm.

**Argument.** Fix a prime p | n and write the points as Fin m x Z/p. The group G = (Z/p)^m of block shifts
rho_s(i, x) = (i, x + s_i) is a p-group and acts by conjugation on the set T of permutations with gcd of cycle
lengths 1 (conjugation keeps cycle lengths). Hence |T| = |T^G| (mod p). A permutation commuting with every
shift keeps each block (else (σy).2 + 1 = (σy).2) and commutes with x -> x+1 on it, so it is a shift rho_s.
rho_s has fixed points on block i when s_i = 0 and only p-cycles otherwise, so rho_s is in T iff some s_i = 0.
Thus |T^G| = p^m - (p-1)^m = (-1)^(m+1) (mod p), and p does not divide a(n).

**Evidence.**
- Lean (Mathlib): [`A079128_mathlib.lean`](A079128_mathlib.lean). Main theorem `A079128_coprime : 1 ≤ n →
  Nat.Coprime (A079128 n) n`, `A079128 n = Nat.card {σ : Perm (Fin n) // RP σ}` with `RP σ`: every d dividing all
  `minimalPeriod σ x` is 1. Uses Mathlib's `IsPGroup.card_modEq_card_fixedPoints`. `tools/leancheck-mathlib.sh`:
  OK, no warnings; axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): brute force over all permutations for n <= 8 (matches the data);
  class-size sums for n <= 60 confirm gcd(a(n), n) = 1 and a(n) = (-1)^(m+1) mod p.
- Outside Lean: none (data agreement checked by the script).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Proved by Kallat (2026, Corollary 6.2), recorded in the entry Oct 30 2026; the
argument here is a different, short p-group fixed-point count. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones of 2026-11-05); no Lean proof known before this.
