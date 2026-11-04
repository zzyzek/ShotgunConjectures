# OEIS A106249: roots of x^n + 1 in the left half-plane (index shift by one)

**Source.** [A106249](https://oeis.org/A106249) (expansion of (1−x+x²+x³)/((1+x)(1+x²)(1−x)²), offset 0), comment
by M. Lagneau (2012): "Conjecture: number of roots of x^n + 1 in the left half-plane for n > 0." (OEIS text, CC BY-SA 4.0.)

**Reading.** Literally a(1) = 0 while x + 1 has the root −1; the statement holds with the index shifted:
a(n) = number of roots of x^(n+1) + 1 with negative real part (n ≥ 0). "Left half-plane" is the open one
(x² + 1 has its roots on the imaginary axis and a(1) = 0).

**Result.** True after the shift by one; false as literally indexed.

**Argument.** The roots of x^m + 1 are exp(iπ(2k+1)/m), 0 ≤ k < m, with negative real part iff
m < 2(2k+1) < 3m: the odd integers in (m/2, 3m/2), of which there are 2⌊m/4⌋ + (m mod 2). The g.f. has
denominator 1 − x − x⁴ + x⁵, and a(n) = 2⌊(n+1)/4⌋ + ((n+1) mod 2) satisfies the recurrence and the five
initial values.

**Evidence.**
- Lean: [`A106249.lean`](A106249.lean): denominator product, initial values, the closed form for all n, and the
  root count for m < 64. Outside Lean: the cosine sign condition and the count for m ≥ 64 (period 4 in m).
- `certificate/check.py`: numeric root counts against the series for n < 200.
- Lean (Mathlib): [`A106249_mathlib.lean`](A106249_mathlib.lean), `A106249_main`: for every n ≥ 0 the x^n coefficient of (1 - x + x^2 + x^3)·((1+x)(1+x^2)(1-x)^2)⁻¹ in ℚ⟦X⟧ equals #{z ∈ ℂ : z^(n+1) = -1, Re z < 0} (`Polynomial.nthRootsFinset`), and the literal indexing fails at n = 1. The cosine sign condition, the root count for all m and the g.f. step are proved there; nothing outside Lean.

**Review level.** `lean-proof` for the shifted statement (Mathlib file above).
**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). Elementary count; the index shift by one is not noted in the entry. Sources: [OEIS A106249 (fetched 2026-11-04)](https://oeis.org/A106249): Lagneau's root-count comment still says Conjecture, unshifted; his cos formula (Nov 2012) restates the count without proof. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A083219, A018837; Google: roots of x^n+1 left half-plane count.
