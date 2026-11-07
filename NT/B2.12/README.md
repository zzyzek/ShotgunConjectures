# Guy UPINT B2: Erdős's extra-weird numbers (partial)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B2 (paraphrased): Erdős asks
whether there are "extra-weird" numbers n, with σ(n) > 3n, such that n is not the sum of distinct divisors of n
in two ways without repetitions. Guy's example: 180 is not one, since σ(180) = 546, 180 = 30 + 60 + 90, and 180
is also the sum of all its other proper divisors except 6.

**Reading.** n is *good* if its proper divisors contain two disjoint sets, each summing to n (Guy's example shows
that "two ways without repetitions" means disjoint sets). Extra-weird = σ(n) > 3n and not good.

**Result (partial; the question stays open).**
1. There is no extra-weird number below 10^12.
2. There is no odd extra-weird number below 10^18.

**Argument.**
- *Multiples.* If d | n and d is good, n is good: multiply both sets of divisors of d by n/d (they stay proper
  divisors of n and disjoint, and each sums to n). Hence a least extra-weird number n has no good proper divisor;
  every 3-abundant proper divisor of n would be good or a smaller extra-weird number, so n is *primitive*
  3-abundant: σ(n) > 3n and σ(n/p) ≤ 3n/p for every prime p | n (abundancy only grows under multiplication).
- *Enumeration.* `certificate/prim3.c` lists all primitive 3-abundant n ≤ X by depth-first search over prime
  factorizations in increasing prime order, pruning a branch when even the product of p/(p-1) over the next primes
  (with product of those primes within the budget X/m) cannot lift σ(m)/m above 3 (exact u128 arithmetic for the
  final tests). Branches stop at the first 3-abundant number. A branch whose σ(m) = 3m exactly (a 3-perfect
  number) is tested for goodness itself and, if good, not extended, since everything below it is a multiple.
  For each listed n a depth-first subset-sum search over the proper divisors (largest first, with suffix-sum
  pruning, plus restarts that forbid one of the 12 largest divisors in the first set) finds two disjoint sets
  summing to n.
- *Counts.* X = 10^12, all n: 15 046 633 primitive 3-abundant numbers tested (not counting multiples of the six
  3-perfect numbers 120, 672, 523776, 459818240, 1476304896, 51001180160, all good), 0 failures; the prime list
  (to 3·10^7) was never exhausted. X = 10^18, odd n only: 1 186 265 odd primitive 3-abundant numbers, 0 failures
  (the least one is 1018976683725 = 3^3·5^2·7^2·11·13·17·19·23·29). Brute-force cross-checks: the primitive list
  matches a direct sieve for n ≤ 3·10^5 (835 numbers); `certificate/xw.c` (sieve of σ, every 3-abundant n tested,
  not only primitive ones) finds no extra-weird n ≤ 3·10^7 (606 506 numbers).

**Evidence.** `certificate/prim3.c` (`prim3 X odd budget`), `certificate/xw.c`. No Lean file: the statement is a
search over 1.6·10^7 numbers with divisor counts up to 20 736, beyond kernel evaluation. Outside Lean: the whole
computation (both C programs; run 2026-11-07, about 15 min for the 10^12 run and 15 min for the odd 10^18 run on
one core).

**Review level.** `agent` (computation; the reduction to primitive 3-abundant numbers is re-derived above).

**Prior art.** Checked 2026-11-07: Guy B2 states the question with no data; web search and OEIS (searches for
"extra-weird", Zumkeller-type sequences A083207, A246198) found no computation of this property;
google-deepmind/formal-conjectures (clone of 2026-11-06) has weird-number files (Erdős #470, OddWeirdNumber) but
not this question. Related: a weird number n with σ(n) > 3n would be extra-weird, so a negative answer would imply
that every weird number has σ(n)/n ≤ 3 (Benkoski–Erdős asked whether σ(n)/n is bounded on weird numbers).
