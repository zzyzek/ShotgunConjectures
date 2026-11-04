# Guy B40: totatives of large n need not contain a Pythagorean triple

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B40. In a 1995 letter Recamán asks whether the set of totatives of
every sufficiently large n (the integers below n and coprime to n) contains a Pythagorean
triple.

**Result.** No, as stated: no n divisible by 2, 3 or 5 has a Pythagorean triple among its
totatives, and there are infinitely many such n. (For n coprime to 30 the question remains;
the scan's note sketches a sieve for that case, not checked here.)

**Argument.** If a² + b² = c², then 2 | ab (two odd squares sum to 2 mod 4, not a square),
3 | ab (two squares prime to 3 sum to 2 mod 3) and 5 | abc (squares prime to 5 are ±1 mod 5;
±1 ± 1 ∈ {0, ±2} mod 5 is never ±1). If p ∈ {2, 3, 5} divides n, every totative of n is prime
to p, so a, b, c cannot all be totatives.

**Evidence.** Lean: [`B40_2.lean`](B40_2.lean), theorem `no_triple`: if 2 | n, 3 | n or
5 | n and gcd(a, n) = gcd(b, n) = gcd(c, n) = 1 then a² + b² ≠ c² (core Lean; axioms propext,
Quot.sound). Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** Partly known: the answer is an immediate corollary of the classical fact that 60 divides abc for every Pythagorean triple; no source found applies it to Recamán's question. The case n coprime to 30 is not addressed. Searched: web, Stumpf's note on the companion question, OEIS. 2026-11-04.
