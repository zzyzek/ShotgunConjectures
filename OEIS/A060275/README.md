# OEIS A060275: the gcd(i, j) = 1 conjecture is true (the triples are disjoint)

**Source.** OEIS [A060275](https://oeis.org/A060275). Original name (Nomoto 2001): numbers
a+b+c = x+y+z with a·b·c = x·y·z, p_k the k-th prime, i = p_a p_b p_c, j = p_x p_y p_z, i ≠ j.
Comment: "Conjecture: we always have gcd(i,j)=1." In Feb 2015 Robert Israel renamed the entry and
replaced the conjecture by "Any two such triples are disjoint", noting that a pair is determined by
its sum and product.

**Result.** True for all positive triples.

**Argument.** If the triples share an entry, the other two pairs have equal sum and product, hence
are equal as multisets ((b − y)(b − z) = 0), so i = j. Thus a, b, c ∉ {x, y, z}, the primes in i and j
are distinct, and gcd(i, j) = 1.

**Evidence.** Lean (Mathlib): [`A060275_mathlib.lean`](A060275_mathlib.lean), `A060275_main`
(`Nat.Coprime i j`, p_k = `Nat.nth Nat.Prime (k − 1)`), `A060275_disjoint`, `A060275_pair`. Axioms
propext, Classical.choice, Quot.sound. Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Known: R. Israel, A060275 edit discussion, 2015-02-10. Not in formal-conjectures or
oeis-lean-proofs (2026-11-07). First Lean proof here.
