# Guy B3 (G. L. Cohen): is every infinitary multiperfect number divisible by 3?

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B3
(unitary perfect numbers). Guy reports Graeme Cohen's infinitary divisors: p^x is an infinitary
divisor of p^y when every binary digit of x is also a digit of y; σ∞(n) is the sum of the
infinitary divisors of n; Cohen conjectures that every n with σ∞(n) = kn (k an integer ≥ 2,
"infinitary multiperfect") is divisible by 3. Reference: G. L. Cohen, On an integer's
infinitary divisors, *Math. Comp.* 54 (1990) 395–411.

**Reading.** σ∞ is multiplicative with σ∞(p^y) = ∏_{i : bit i of y is 1} (1 + p^(2^i)).
Equivalently, n is uniquely a product of distinct "Fermi–Dirac primes" q = p^(2^i), and
σ∞(n) = ∏ (1 + q) over them. k = 1 (n = 1) is excluded.

**Result (partial; the conjecture stays open).**

1. *Computation (all k).* Every n ≤ 2·10¹⁰ with σ∞(n) ≡ 0 (mod n), n > 1, is divisible by 3.
   The complete list in this range is 6, 60, 90, 120, 36720, 73440, 12646368, 22276800,
   44553600, 126463680, 133660800, 252927360, 758782080, 4201148160, 8402296320, i.e. the
   terms of OEIS A007358 below the bound, so that list is complete up to 2·10¹⁰.
2. *Structure of a counterexample (elementary).* Let 3 ∤ n and σ∞(n) = kn.
   (a) If 3 ∤ k, then every prime p ≡ 2 (mod 3), including p = 2, divides n to an even power:
   an odd exponent puts the factor 1 + p ≡ 0 (mod 3) into σ∞(n) = kn.
   (b) If 3 | k, then v₃(k) = Σ v₃(1 + p) over the primes p ≡ 2 (mod 3) (including 2) with odd
   exponent in n; in particular k is divisible by 3 at least once per such prime.
   (c) n is even (Cohen): for odd n with t Fermi–Dirac factors, 2^t | σ∞(n) = kn forces
   2^t | k, but k = ∏(1 + 1/q) < 2^t.

**Argument.** Item 1: segmented sieve computing σ∞(n) exactly (128-bit) from the
factorisation for every n, `certificate/isig.c`; the run was split at 8.4·10⁹ (logs
`isig_part1.txt`, sequential output up to 8402296320, and `isig_part2.txt` with progress
lines). The program reproduces A007358 below 2·10⁸. Item 2 is the displayed one-line
arguments.

**Evidence.** `certificate/` holds the program and logs. No Lean (the content is a sieve run
and three one-line remarks). Outside Lean: the sieve computation.

**Review level.** agent.

**Prior art (2026-11-07).** Cohen 1990 (no odd ones; conjecture). OEIS A007357 (k = 2): Jeff
Sponaugle (2026) reports no infinitary perfect number below 10²⁸ beyond the list, all divisible
by 3, so for k = 2 the conjecture is verified far beyond item 1; the all-k search here is
what is new, and it is small. OEIS A007358 (all k) is marked as not exhaustive. MathWorld
"Infinitary Multiperfect Number". google-deepmind/formal-conjectures: no entry.
