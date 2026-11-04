# Guy F19: every n ≥ 23 has two 3-part partitions with equal product

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F19. The first edition asked whether, writing n = a + b + c with
0 < a < b < c in every possible way, all products abc are distinct (Leech: no). Recamán
suggests the opposite: every sufficiently large n has two such partitions with equal products.

**Result.** True: every n ≥ 23 has two different partitions n = a + b + c, 0 < a < b < c,
with equal products. The exceptions are exactly n ≤ 18 and n = 22. (Allowing equal parts,
0 < a ≤ b ≤ c, the exceptions are n ≤ 12, 15 and 18.)

**Argument.** For t ≥ 37 and 0 ≤ s, w ≤ 18 put
A = (2t + 2s, 8t + 2s + 2w, 9t + 3w) and B = (3t + 3s, 4t + s + w, 12t + 4w).
Both sum to 19t + 4s + 5w and both have product 12(t + s)(4t + s + w)(3t + w)
(A = (2x, 2y, 3z), B = (3x, y, 4z) with x = t + s, y = 4t + s + w, z = 3t + w). For t ≥ 37 the
parts are strictly increasing in each triple and A ≠ B. Since 4s + 5w (0 ≤ s, w ≤ 18) takes
every residue mod 19 with 4s + 5w ≤ 162, every n ≥ 19·37 + 162 = 865 is covered. The range
23 ≤ n ≤ 864 is an explicit table.

**Evidence.**
- Lean: [`F19_1.lean`](F19_1.lean), theorem `recaman`: for all n ≥ 23 the two partitions
  exist (core Lean; axioms propext, Quot.sound).
- Lean + Mathlib: [`F19_1_mathlib.lean`](F19_1_mathlib.lean), `F19_1_main`: for every n, the strict version
  holds iff n ≥ 19 and n ≠ 22, and the equal-parts version iff n ∉ {0..12, 15, 18} (n ≤ 22 by a Bool check
  over all partitions, proved equivalent to the definitions). Outside Lean: nothing.
- `certificate/f191_check.py` (second reader): failures for n ≤ 1500 under both conventions,
  family check 865 ≤ n ≤ 20000. `f191_table.py` generates the Lean table. Scan scripts copied.

**Review level.** `lean-proof`: the full result, including the exceptions under both conventions, in [`F19_1_mathlib.lean`](F19_1_mathlib.lean).
**Prior art.** Known: Kelly, Proc. Amer. Math. Soc. 15 (1964) (cited in the book) proves s₂(3) = 23 (every n ≥ 23 has two 3-part partitions with equal product and all six parts distinct, stronger than ours) and s*₂(3) = 19 without distinctness, matching our exceptions; restated in [Cha et al., arXiv 1811.07451](https://arxiv.org/abs/1811.07451). Our result is a re-proof. 2026-11-04.
