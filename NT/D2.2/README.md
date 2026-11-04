# Guy D2: x^n + y^n = n!·z^n has a solution with n = 3

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D2. Erdős asks for a proof that x^n + y^n = n!·z^n has no integer
solutions with n > 2 (nontrivial ones, xyz ≠ 0, understood).

**Result.** False for n = 3: 17³ + 37³ = 4913 + 50653 = 55566 = 6·21³. The case n = 4 has
no nontrivial solution (fourth powers are 0 or 1 mod 16 and 24z⁴ ≡ 0 or 8 mod 16, so x, y, z
are all even and descent applies). The cases n ≥ 5 are not addressed.

**Argument.** Direct computation.

**Evidence.** Lean: [`D2_2.lean`](D2_2.lean) (`decide`, no axioms; from
`../open-problems/lean/Witnesses1.lean`). `certificate/d2_fact_fermat.py` is the scan's search.

**Review level.** `lean-proof` (of the counterexample).
**Prior art.** Known: [S. K. Jena, Commun. Math. 26 (2018) 11–14](https://cm.episciences.org/9473/pdf) refutes the problem with the same 37³ + 17³ = 3!·21³ and infinitely many primitive solutions ([OEIS A173518](https://oeis.org/A173518)); 6 = (17/21)³ + (37/21)³ is classical. Jena leaves n ≥ 4 open; our n = 4 remark is a routine mod-16 descent. 2026-11-04.
