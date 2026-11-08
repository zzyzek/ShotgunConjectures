# OEIS A173263: the sequence is infinite (Israel 2015), so "finite and complete" is false

**Source.** OEIS [A173263](https://oeis.org/A173263) (Jasinski 2010): n such that ChebyshevT(n/2, n) is
not an integer. Old comment: "Conjecture: This sequence is finite and complete" (data ended at 87).
Removed by Robert Israel on 2015-04-30: Jasinski's stop at 87 came from roundoff; T(n/2, n) is
irrational when not an integer.

**Result.** False (known): the terms are all odd n not of the form 2k² − 1 (A056220), an infinite set.

**Argument (Israel, entry comments).** T(1/2, n) = sqrt((n+1)/2). For odd k, T_k(x) = x·P(x²) with P
integral and without roots ≥ 1, so T(k/2, n) = T_k(T(1/2, n)) = sqrt((n+1)/2)·P((n+1)/2), which is an
integer iff (n+1)/2 is a square and irrational otherwise.

**Evidence.** Lean: [`A173263_mathlib.lean`](A173263_mathlib.lean), checked (axioms propext,
Classical.choice, Quot.sound). ChebyshevT(ν, x) is defined as cosh(ν arcosh x) for x >= 1 (Mathlib
`Real.arcosh`), which agrees with the Chebyshev polynomial for integer ν (`T_real_cosh`).
`A173263_main`: for n >= 1, ChebyshevT(n/2, n) is not an integer iff n is odd and (n+1)/2 is not a
square. `A173263_infinite`: the set is infinite (it contains 2(k+1)^2 + 1). Outside Lean: none.

**Review level.** `lean-proof` (Lean, Mathlib).

**Prior art.** R. Israel, A173263 comments and edit discussion, 2015-04-30/05-01 (history checked
2026-11-07). Not in formal-conjectures or oeis-lean-proofs.
