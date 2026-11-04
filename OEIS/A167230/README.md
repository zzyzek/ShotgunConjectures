# OEIS A167230: entries of exp(Sierpiński triangle)/e are Bell numbers

**Source.** OEIS [A167230](https://oeis.org/A167230): the matrix exponential of Sierpiński's
triangle S (Pascal's triangle mod 2, A047999) divided by e. Conjecture: "All the nonzero entries
in this triangle are Bell numbers (A000110)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Entry (n,k) is Bell(j) when k AND n = k (bitwise), j = popcount(n) -
popcount(k), and 0 otherwise.

**Argument.** By Lucas's theorem, S(n,k) = prod_i M(n_i, k_i) over binary digits with
M = [[1,0],[1,1]], i.e. S is the (infinite) Kronecker power of M. Hence S^m is the Kronecker power
of M^m = [[1,0],[m,1]], so S^m(n,k) = m^j if k ⊆ n bitwise (j = number of bits set in n but not
in k), else 0. Then exp(S)(n,k) = sum_m m^j/m! = e·Bell(j) by Dobinski's formula.

**Evidence.**
- `certificate/a167230.py`: the formula for S^m checked exactly for 64×64 and m ≤ 6; Dobinski
  sums against Bell(j), j < 8, numerically.
- Lean (Mathlib): [`A167230_mathlib.lean`](A167230_mathlib.lean), theorem `A167230_conjecture`: with S(n,k) =
  C(n,k) mod 2, S^m its matrix powers and exp(S)(n,k) = Σ_m S^m(n,k)/m! (real tsum), exp(S)(n,k)/e = B(j) if k ⊆ n
  bitwise (`bsub`, equivalent to the `testBit` condition by `bsub_iff_testBit`), j = number of bits of n not in k,
  and 0 otherwise (`A167230_nonzero`: every nonzero entry is a Bell number). Lucas's theorem from Mathlib;
  S^m(n,k) = m^j and Dobinski's formula (Bell numbers by their recurrence) are proved in the file. Nothing outside
  Lean.

**Review level.** `lean-proof`.

**Depends on (Mathlib).** Lucas's theorem (in Mathlib), Dobinski's formula (series), matrix
exponential of a lower-triangular infinite matrix entrywise.

**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). No proof found. Short proof: the Sierpinski matrix is the zeta matrix of the Boolean lattice (Lucas), so its m-th power has entries m^j, and Dobinski's formula gives Bell(j). Sources: [OEIS A167230 (fetched 2026-11-04)](https://oeis.org/A167230): still says Conjecture. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; Google: matrix exponential Sierpinski triangle Bell numbers.
