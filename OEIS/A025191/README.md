# OEIS A025191: row half-sums of A025177 are first differences of A027914 and of A081673/2

**Source.** OEIS [A025191](https://oeis.org/A025191) (offset 0): a(n) = Σ_{k=0..n} T(n,k), T = A025177.
Comment: "Conjectures: a(n) = A027914(n)-A027914(n-1) = (A081673(n)-A081673(n-1))/2."

**Reading.** A027907(n,k) = [x^k](1+x+x²)^n; A025177(n,k) = A027907(n,k) − A027907(n−1,k−1) (first differences in
the n,n direction; g.f. (1−yz)/(1−z(1+y+y²))); A027914(n) = Σ_{k≤n} A027907(n,k); A081673 has e.g.f.
exp(3x) − exp(x)(1 − I₀(2x)) with I₀(2x) = Σ_j x^(2j)/(j!)². Both conjectured identities for n ≥ 1
(A027914(−1) is undefined).

**Result.** True for every n ≥ 1.

**Argument.** Σ_{k≤n} A027907(n−1,k−1) = Σ_{j≤n−1} A027907(n−1,j) = A027914(n−1), which gives the first identity.
For the second: rows of A027907 are palindromic and sum to 3^n, so 2·A027914(n) = 3^n + A027907(n,n);
writing 1+x+x² = x + (1+x²) gives A027907(n,n) = Σ_{m even} C(n,m) C(m,m/2); the e.g.f. gives
A081673(n) = 3^n − 1 + Σ_{m even} C(n,m) C(m,m/2). Hence A081673(n) = 2·A027914(n) − 1.

**Evidence.**
- Lean (Mathlib): [`A025191_mathlib.lean`](A025191_mathlib.lean). `A025191_conjecture (n : ℕ) (hn : 1 ≤ n) :
  A025191 n = A027914 n − A027914 (n−1) ∧ (A025191 n : ℚ) = (A081673 n − A081673 (n−1))/2`, with A081673 defined from
  its e.g.f. in ℚ⟦X⟧. Supporting: `A025191_tri_symm`, `A025191_row_sum`, `A025191_two_A027914`, `A025191_central`,
  `A081673_formula`, `A081673_eq`. Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: all definitions against the entries' terms; both identities for n < 40.
- Outside Lean: that I₀(2x) = Σ x^(2j)/(j!)² (the series of the Bessel function). The OEIS terms are checked in
  Python only (the Lean polynomial coefficients are noncomputable).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: OEIS A025191, A025177, A027914, A081673 entries (A027914 prints
a(n) = (3^n + A002426(n))/2, from which the identities follow quickly), web search, google-deepmind/formal-conjectures
(no file). No written proof found.
