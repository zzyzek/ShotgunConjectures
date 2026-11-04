# OEIS A113610: local minima of composite digit sums do not mark twin primes

**Source.** [A113610](https://oeis.org/A113610) (sum of the digits of all composites strictly between prime(n) and
prime(n+1)), comment: "Conjecture: For n > 9 if a(n) > a(n+1) < a(n+2) then prime(n) and prime(n+1) form a twin
prime pair." (OEIS text, CC BY-SA 4.0.)

**Result.** False, in the literal reading and in the variant where the local minimum a(n+1) belongs to a twin gap.

**Argument.** n = 12: a(12) = 27 > a(13) = 6 < a(14) = 27 (composites 38, 39, 40 | 42 | 44, 45, 46), but
prime(12) = 37, prime(13) = 41 are not twins. Variant (prime(n+1), prime(n+2) twins): n = 21 has
a(21) = 65 > a(22) = 27 < a(23) = 70, with prime(22) = 79, prime(23) = 83. Below 10^5 there are 3194 literal and
1981 variant failures.

**Evidence.**
- Lean: [`A113610.lean`](A113610.lean) (`decide`): the primes below 90 and the six values. Nothing outside Lean.
- `certificate/check.py`: the scan up to 10^5.

**Review level.** `lean-proof`.
**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). Counterexample n = 12 is not recorded anywhere found. Sources: [OEIS A113610 (fetched 2026-11-04)](https://oeis.org/A113610): still says Conjecture; no counterexample. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google: A113610.
