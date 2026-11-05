# OEIS A123723: multiples of 4 in the list, other than 4, are 4p with p prime

**Source.** OEIS [A123723](https://oeis.org/A123723) (J. W. Layman, 2006): values of n with
A000224(n) = ⌈(n+1)/4⌉ (1, 4, 8, 12, 20, 28, 44, 45, ...; offset 1). Comment: "If n>4 and a(n)
is a multiple of 4, then a(n)/4 is a prime." (OEIS text, CC BY-SA 4.0.)

**Reading.** ⌈(n+1)/4⌉ = ⌊n/4⌋ + 1. Since a(4) = 12, "n > 4" means a(n) > 12. The proof covers
every multiple N ≠ 4, including N = 8 = 4·2.

**Result.** Proved.

**Argument.** The general lemmas are those of [A123722](../A123722/README.md): S is
multiplicative, S(m) ≤ ⌊m/2⌋ + 1, odd m with 2S(m) = m + 1 is 1 or prime, and S(N) ≤ S(M)·N/M
for M | N. Write N = 2^j·r with r odd and j ≥ 2, and S(N) = N/4 + 1.
- j = 2: 2S(r) = r + 1, so r is prime (r = 1 gives N = 4).
- j = 3: 3S(r) = 2r + 1 and 2S(r) ≤ r + 1 force r = 1, so N = 8 and N/4 = 2.
- j ≥ 4 and r ≥ 3: squares mod 8 are 0, 1, 4, so S(2^j) ≤ 3·2^(j−3). That makes
  2S(N) ≤ 3·2^(j−3)(r+1), which is less than 2^(j−1)r + 2.
- j ≥ 4 and r = 1: S(16) = 4 ≠ 5. For j ≥ 5, mod 32 has 7 squares, so
  S(2^j) ≤ 7·2^(j−5) < 2^(j−2) + 1.

**Evidence.**
- [`A123723_mathlib.lean`](A123723_mathlib.lean) (Mathlib). `A123723_main` proves the statement
  for a(n) = `Nat.nth` of the set (offset 1), and `A123723_classify` proves it for every member.
  `A123723_four_mul_prime` shows that 4p is a member for every odd prime p. `A123723_data` checks
  the members below 64. Axioms: propext, Classical.choice, Quot.sound. Outside Lean: nothing.
- `certificate/check.py` is a brute-force check (n < 6000).

**Review level.** lean-proof.

**Prior art (2026-11-05).** The OEIS entry still marks this as a conjecture. A web search found no
proof. google-deepmind/formal-conjectures has no file for A123723.
