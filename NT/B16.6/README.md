# Guy B16: 46 and 430 are the two smallest composite exceptions to the Ankeny–Artin–Chowla property

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section B16. The Ankeny–Artin–Chowla conjecture says that for a prime
p ≡ 1 (mod 4), p does not divide u, where (t, u) is the least positive solution of
t² − p u² = 1. Guy notes the statement fails for non-prime d and that Myerson believes
46 and 430 are the two smallest counterexamples.

**Reading.** d ranges over non-square, non-prime integers > 1 and (t, u) is the least
positive solution of the Pell equation t² − d u² = 1, as in the book's wording.

**Result.** True. Among non-square non-prime d ≤ 430, d | u only for d = 46
((t, u) = (24335, 3588), u = 78·46) and d = 430 ((t, u) = (2862251, 138030), u = 321·430).

**Argument.** The least solution is the convergent of the continued fraction of √d at the end
of the first period (second period when the period length is odd). Computing it for every
non-square non-prime d ≤ 430 and testing d | u gives the two values.

**Evidence.**
- Lean (Mathlib): [`B16_6_mathlib.lean`](B16_6_mathlib.lean) proves `B16_6_main`: for every d with 2 ≤ d ≤ 430, d not a square and not prime, and every fundamental solution a of x² - d y² = 1 (Mathlib `Pell.Solution₁`, `Pell.IsFundamental`), d ∣ a.y ↔ d = 46 ∨ d = 430; `B16_6_values` gives the two fundamental solutions. Minimality for 46 and 430 by a kernel check that 1 + d y² is not a square for 0 < y < u, plus Mathlib's uniqueness of the fundamental solution; for the other 326 values of d a solution (t, u) with d ∤ u (computed outside, checked by the kernel) suffices, since every positive solution is a power of the fundamental one (Mathlib `IsFundamental.eq_pow_of_nonneg`) and y(a) ∣ y(aⁿ). Outside Lean: nothing.
- Lean: [`B16_6.lean`](B16_6.lean) checks both Pell identities and the divisibilities.
  Outside Lean: minimality of the two solutions and the scan over the other d.
- `certificate/b166_check.py` (second reader, own code): continued fractions for all d ≤ 430;
  brute-force confirmation that 3588 is the least u for d = 46.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`B16_6_mathlib.lean`](B16_6_mathlib.lean)).
**Prior art.** Partly known: for squarefree d the list of d dividing the y of the fundamental unit begins 46, 430, 1817 ([OEIS A135735](https://oeis.org/A135735); Stephens–Williams, Math. Comp. 50 (1988); [Reinhart, arXiv 2402.09827](https://arxiv.org/abs/2402.09827); [Fellini, arXiv 2410.20934](https://arxiv.org/abs/2410.20934)). Not covered there: non-squarefree non-square d ≤ 430 (our Pell-equation reading), a finite computation. 2026-11-04.
