# NT-B36.2 (Guy B36): solutions of phi(n+3) = phi(n) + 2 lie in two prime-power families

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., B36 (paraphrased): is 5186 the only n with
phi(n) = phi(n+1) = phi(n+2)? Does phi(n+k) = phi(n) + phi(k) have a solution for k = 3? McCranie found none of
either below 10^10 (apart from 5186).

**Result.** Partial (k = 3). Every solution of phi(n+3) = phi(n) + 2 has, for a prime p = 3 (mod 4) and a >= 1,
either (A) n = 2p^a and phi(2p^a + 3) = p^(a-1)(p-1) + 2, or (B) n = 2p^a - 3 and phi(2p^a - 3) = p^(a-1)(p-1) - 2.
In case (A) with a = 1, m = 2p + 3 is a composite with 2 phi(m) = m - 1, hence phi(m) | m - 1: a counterexample to
Lehmer's totient conjecture. Both questions remain open; the triple question is known to have no further
solution below 10^15 (OEIS A001274, J. McCranie, Jan 2026).

**Argument.** phi(m) = 2 (mod 4) iff m is 4, p^a or 2p^a with p = 3 (mod 4) (each odd prime p contributes the
factor p - 1, which is 0 mod 4 unless p = 3 mod 4, and 2^b contributes 2^(b-1)). For n >= 3 both phi(n) and
phi(n+3) are even; if both were 0 mod 4 their difference would be too, so n or n+3 is of that form. If n = p^a,
n+3 is even and phi(n+3) <= (p^a + 3)/2 < p^(a-1)(p-1) + 2; if n+3 = p^a, n is even and
phi(n) <= (p^a - 3)/2 < p^(a-1)(p-1) - 2 (p >= 3); n = 4 and n = 1 fail. This leaves n = 2p^a (A) and
n + 3 = 2p^a (B). In (A) with a = 1: phi(2p+3) = p + 1 = (m-1)/2 for m = 2p+3, and m prime would give
phi(m) = m - 1.

**Evidence.** Lean (Mathlib): [`B36_2_mathlib.lean`](B36_2_mathlib.lean), theorems `B36_2_reduction` (the two
families), `B36_2_totient_mod4` (the mod-4 characterisation) and `B36_2_lehmer` (family n = 2p gives a composite m
with phi(m) | m - 1). Checked with tools/leancheck-mathlib.sh; axioms propext, Classical.choice, Quot.sound.
certificate/red.py checks the characterisation numerically for m < 2*10^5 and finds no k = 3 solution below
3*10^6; certificate/seg.c (segmented sieve) re-verifies both questions to 10^8.
Outside Lean: the computations (no-solution ranges) and the literature status of the triple question.

**Review level.** Lean-checked reduction; computations rerun once.

**Prior art.** Guy B36, OEIS A001274 and A110172, web search (checked 2026-11-08); the reduction and the Lehmer
link were not found stated.
