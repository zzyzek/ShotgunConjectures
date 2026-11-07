# OEIS A219431: a(odd) ≡ 2 and a(even) ≡ 0 (mod 4)

**Source.** OEIS [A219431](https://oeis.org/A219431), logarithmic derivative of the g.f. of the
overpartitions of n² (A219430(n) = A015128(n²)). Comment: "Conjecture: a(2*n+1) == 2 (mod 4),
a(2*n) == 0 (mod 4)." (OEIS text, CC BY-SA 4.0.) A219430 states the equivalent form "log derivative
≡ 2x/(1 − x²) (mod 4)" as a conjecture too.

**Reading.** G(x) = Σ_{n≥0} A219430(n) xⁿ and Σ_{n≥1} a(n) xⁿ = x G′(x)/G(x), i.e.
Σ_{k=1}^{n} a(k) A219430(n−k) = n A219430(n) for n ≥ 1.

**Result.** True for all n ≥ 1.

**Argument.**
1. An overpartition of m is a partition in which the first occurrence of each part size may be overlined, so
   p̄(m) = Σ_λ 2^{d(λ)}, d(λ) = number of distinct part sizes. For m ≥ 1, d ≥ 1 and 2^d ≡ 0 (mod 4) for d ≥ 2,
   so p̄(m) ≡ 2·#{λ ⊢ m with one part size} = 2τ(m) (mod 4) (one part size s ⇔ s | m).
2. τ(n²) = Π (2e_p + 1) is odd, so b(n) := A219430(n) ≡ 2 (mod 4) for n ≥ 1, and b(0) = 1.
3. a(n) = n b(n) − Σ_{k=1}^{n−1} a(k) b(n−k). By strong induction all a(k) are even, so each a(k) b(n−k)
   is ≡ 0 (mod 4), and a(n) ≡ n b(n) ≡ 2n (mod 4).

**Evidence.**
- Lean (Mathlib): [`A219431_mathlib.lean`](A219431_mathlib.lean). `overpart m` = Σ over `m.Partition` of
  2^(distinct parts), `A219430 n = overpart (n^2)`. `A219431_main`: any a with
  Σ_{k=1}^{n} a(k) A219430(n−k) = n A219430(n) (n ≥ 1) has a(2n+1) % 4 = 2 and a(2n) % 4 = 0 (n ≥ 1).
  Steps `overpart_mod4`, `card_single`, `divisors_sq_odd`, `A219430_mod4`, `logderiv_mod4`.
  Axioms propext, Classical.choice, Quot.sound; zero warnings.
- [`certificate/check.py`](certificate/check.py): Σ 2^{d(λ)} equals the coefficients of Π (1 + x^k)/(1 − x^k)
  for m ≤ 25; the recurrence reproduces the entry's a(1..9); the pattern holds for n ≤ 60.
- Outside Lean: none beyond the reading (overpartition count as Σ 2^{d(λ)}; log derivative as the
  coefficient identity).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. p̄(m) ≡ 2 (mod 4) exactly when m is a nonzero square is classical
(it follows from 1/θ₄(q) = Σ p̄(m) qᵐ; e.g. Hirschhorn–Sellers, Arithmetic relations for overpartitions,
JCMCC 53 (2005)). The congruence for the logarithmic derivative is still listed as a conjecture in A219431 and
A219430; web search found no proof. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
