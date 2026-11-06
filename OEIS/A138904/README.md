# OEIS A138904: rotational symmetries of a binary expansion

**Source.** OEIS [A138904](https://oeis.org/A138904) (Max Sills, 2008), a(m) = number of rotational
symmetries of the binary expansion of m. Two conjectures in the comments (OEIS text, CC BY-SA 4.0):
"For binary expansions of length n, there are d(n) distinct values that will show up as symmetries
... precisely the divisors of n", and, for n whose proper divisors are all coprime, "only one number
of length n with n symmetries ... 2^n - 1"; for each proper divisor d > 1 the numbers with n/d
symmetries are (2^0 + 2^d + ... + 2^(n-d))·a with 2^(d-1) <= a < 2^d - 1; "the rest ... only the
trivial symmetry".

**Reading.** a(m) counts the rotations k in {0, ..., L-1} of the L-bit word of m (L = binary length,
m = 0 is "0") that give the same word; a(0..98) agree with the data. "Proper divisors all coprime" is
read as: the divisors of L strictly between 1 and L are pairwise coprime (L = 1, p, p^2 or pq).

**Result.** Both conjectures hold.
1. For m of length L, a(m) divides L, and every divisor of L is a(m) for some m of length L.
2. a(m) = L only for m = 2^L - 1. For every prime d dividing L with d < L (any L, not only the
   coprime-divisor case), a(m) = L/d exactly when m = R·a, R = 1 + 2^d + ... + 2^(L-d),
   2^(d-1) <= a < 2^d - 1. If the divisors of L strictly between 1 and L are pairwise coprime, every
   such divisor is prime, so all other m of length L have a(m) = 1.

**Argument.** Let S = {k : rotation by k fixes the word}. S is closed under addition and under
k, j -> j - k (indices mod L), so with p the least positive element, S = {multiples of p} and p | L;
hence a(m) = L/p divides L. The word with a single 1 at the top of each block of length q = L/e has
least period q, so a = e. a(m) = L means period 1, so all bits equal the top bit 1. Period d means
the word is its low d-bit block a repeated, i.e. m = R·a, with top bit of a set (a >= 2^(d-1)); the
least period then divides d, and for prime d it is 1 or d, and 1 only for a = 2^d - 1. If proper
divisors are pairwise coprime, a composite proper divisor d would share its prime factor r < d with
itself as a divisor pair (r, d), so every proper divisor is prime.

**Evidence.**
- Lean (core): [`A138904.lean`](A138904.lean): `symCount_dvd`, `A138904_dvd`, `A138904_values`
  (conjecture 1), `A138904_eq_length_iff`, `A138904_prime_block`, `A138904_rest` (conjecture 2),
  `A138904_terms` (a(0..20) by `decide`). Axioms propext, Classical.choice, Quot.sound.
  Outside Lean: that `A138904` (rotations read through `Nat.testBit`, length `Nat.log2 m + 1`) is
  the OEIS definition; `certificate/check.py` compares it with the 99 listed terms and re-checks
  both conjectures for lengths up to 16.

**Review level.** `lean-proof`.

**Prior art.** Known in substance: the rotations fixing a cyclic word form a subgroup of Z/L, and a
word equals a proper rotation of itself iff it is a power of a shorter word (Lyndon-Schützenberger;
Lothaire, *Combinatorics on Words*, Prop. 1.3.2). The OEIS entry still lists both statements as
conjectures; related A137323 gives counts without proof. No Lean proof found
(google-deepmind/formal-conjectures has no OEIS/138904.lean; otoi-lab/oeis-lean-proofs has no
entry). Searched OEIS entry and history, web, arXiv. Checked 2026-11-06.
