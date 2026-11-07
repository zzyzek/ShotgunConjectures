# OEIS A173263: the sequence is infinite (Israel 2015), so "finite and complete" is false

**Source.** OEIS [A173263](https://oeis.org/A173263) (Jasinski 2010): n such that ChebyshevT(n/2, n) is
not an integer. Old comment: "Conjecture: This sequence is finite and complete" (data ended at 87).
Removed by Robert Israel on 2015-04-30: Jasinski's stop at 87 came from roundoff; T(n/2, n) is
irrational when not an integer.

**Result.** False (known): the terms are all odd n not of the form 2k² − 1 (A056220), an infinite set.

**Argument (Israel, entry comments).** T(1/2, n) = sqrt((n+1)/2). For odd k, T_k(x) = x·P(x²) with P
integral and without roots ≥ 1, so T(k/2, n) = T_k(T(1/2, n)) = sqrt((n+1)/2)·P((n+1)/2), which is an
integer iff (n+1)/2 is a square and irrational otherwise.

**Evidence.** Citation (literature-likely item; a Lean proof needs the real Chebyshev function of
non-integer degree, more than the time cap). `lean_status: needs-mathlib`. Outside Lean: the whole
argument.

**Review level.** `rechecked` (argument re-derived by hand).

**Prior art.** R. Israel, A173263 comments and edit discussion, 2015-04-30/05-01 (history checked
2026-11-07). Not in formal-conjectures or oeis-lean-proofs.
