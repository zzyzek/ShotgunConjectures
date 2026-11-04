# OEIS A215462: 2n is a sum of two odd nonprimes for n > 19; eventual ordering

**Source.** OEIS [A215462](https://oeis.org/A215462): number of ordered decompositions of 2n into
two odd nonprimes (1 counts as nonprime). Conjectures: "a(n) is never zero for n > 19, verified to
10^9" and "a(n) > A215461(n) > A002372(n) for sufficiently large n." (OEIS text, CC BY-SA 4.0.)

**Result.** Both true.

**Argument.**
- Conjecture 1. 9, 25, 35 are odd nonprimes with residues 0, 1, 2 mod 3, so for one of them c,
  d = 2n - c is divisible by 3; d is odd, and for n ≥ 22, d ≥ 9, so d is nonprime. n = 20: 40 =
  25 + 15; n = 21: 42 = 15 + 27.
- Conjecture 2. The n ordered pairs (2i+1, 2j+1) with i + j = n - 1 split as
  A002372(n) + A215461(n) + a(n) = n (stated in the entry). Let π' be the number of odd primes
  below 2n and G = A002372(n) (ordered prime pairs). Each odd prime p < 2n pairs with 2n - p, so
  A215461(n) = 2(π' - G) and a(n) = n - 2π' + G. Hence a(n) > A215461(n) iff n + 3G > 4π', true
  for large n since π' ~ 2n/log(2n) = o(n); and A215461(n) > G iff 2π' > 3G, true for large n
  since G ≪ n/log^2 n (Brun–Selberg sieve upper bound) while π' ≫ n/log n (Chebyshev).

**Evidence.**
- [`A215462.lean`](A215462.lean): `witness`, conjecture 1 for every n > 19 (core Lean).
  Outside Lean: that the chosen numbers are nonprime (factor 3 or 5); conjecture 2.
- Lean (Mathlib): [`A215462_mathlib.lean`](A215462_mathlib.lean), `A215462_conj1` / `A215462_card_pos`: for every n > 19 there are odd c, d with c + d = 2n and both not `Nat.Prime` (so a(n) > 0). Outside Lean: conjecture 2 (needs an O(n/log² n) bound for Goldbach representations, Brun or Selberg sieve; not in Mathlib).

**Review level.** `lean-witness`: conjecture 1 is `lean-proof` (Mathlib file above); conjecture 2 is re-derived (`rechecked`) and outside Lean.

**Depends on (Mathlib).** Conjecture 2: Chebyshev bounds for π(x) (Mathlib has them), and an upper
bound G(n) = O(n/log^2 n) for Goldbach representations (Brun or Selberg sieve; not in Mathlib).

**Prior art.** Partly known. Conjecture 1 is classical: every even number > 38 is a sum of two odd composites ([1984 AIME Problem 14](https://artofproblemsolving.com/wiki/index.php/1984_AIME_Problems/Problem_14), [ProofWiki](https://proofwiki.org/wiki/Positive_Even_Integers_not_Expressible_as_Sum_of_2_Composite_Odd_Numbers)). Conjecture 2 is a routine consequence of Chebyshev and the Brun-Selberg sieve bound; not found stated. [OEIS A215462](https://oeis.org/A215462) (fetched 2026-11-04) still states both. Searched: entry, OEIS cross-reference search, edit history, web. Worth an OEIS comment. (Prior-art review 2026-11-04.)
