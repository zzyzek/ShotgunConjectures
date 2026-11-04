# OEIS A072901: composites with disc Q(√n) = 4n are squarefree

**Source.** [A072901](https://oeis.org/A072901) (composite n with discriminant of Q(√n) equal to 4n),
comment by V. Librandi and M. Marcus: "Conjecture: All terms are squarefree." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** Write n = d·s^2 with d squarefree (d > 1, as n is not a square). Q(√n) = Q(√d) has
discriminant d (d ≡ 1 mod 4) or 4d (d ≡ 2, 3 mod 4), at most 4d. If s ≥ 2 this is < 4n. So
discriminant 4n forces s = 1 (and n ≡ 2, 3 mod 4).

**Evidence.**
- Lean (Mathlib): [`A072901_mathlib.lean`](A072901_mathlib.lean) proves `A072901_discr`: for n not a square, `NumberField.discr` of Q(√n) (Mathlib `QuadraticAlgebra ℚ n 0`) equals 4n iff n is squarefree and n ≡ 2, 3 (mod 4); `A072901_conjecture`: hence composite n with disc Q(√n) = 4n are squarefree. The quadratic-field discriminant (d for squarefree d ≡ 1 mod 4, else 4d; ring of integers Z[(1+√d)/2] or Z[√d]) is proved in `lib/OpenProblemsLib/R5_Quadratic.lean` (`discr_sqrt`). Also `A072901_main`: 4n is a fundamental discriminant (Mathlib `Int.IsFundamentalDiscr`) iff n is squarefree and n ≡ 2, 3 (mod 4). Outside Lean: none.
- `certificate/check.py`: n < 10^5, discriminant = 4n iff n squarefree and n ≡ 2, 3 (mod 4).

**Review level.** `lean-proof`: the result, stated with Mathlib's `NumberField.discr` of Q(√n), is proved in Lean + Mathlib ([`A072901_mathlib.lean`](A072901_mathlib.lean)); nothing outside Lean.
**Prior art.** Known: the discriminant of Q(sqrt(n)) is 4n exactly when n is squarefree and n == 2, 3 (mod 4) (textbook algebraic number theory). [A072901](https://oeis.org/A072901) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
