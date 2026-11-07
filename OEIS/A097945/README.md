# OEIS A097945: Sum mu(n)/phi(n) = 0

**Source.** OEIS A097945, a(n) = mu(n)·phi(n) (G. McGarvey, 2004). Comment: "Conjecture:
Sum_{n>=1} mu(n)/phi(n) = Sum_{n>=1} a(n)/phi(n)^2 = 0", followed by a pairing argument for
exponents s > 1 and a second conjecture, Sum mu(n)/phi(n)^z = 0 for Re(z) > 1 (entry checked
2026-11-06, last edit Apr 08 2026; the conjecture is unchanged). Listed in the OEIS wiki page
Talk:Conjectures/List.

**Reading.** a(n)/phi(n)^2 = mu(n)/phi(n), so both series are the same. For s = 1 the series
does not converge absolutely (Sum |mu(n)|/phi(n) diverges); "= 0" is read as convergence of the
partial sums Sum_{n<=N} in the natural order to 0. For Re(z) > 1 the series converges absolutely.

**Result.**
1. For every complex z with Re z > 1, Sum mu(n)/phi(n)^z = 0 (absolutely convergent).
   Unconditional, proved in Lean.
2. Sum_{n<=N} mu(n)/phi(n) → 0. Proved in Lean, using Sum_{m<=N} mu(m)/m → 0 (von Mangoldt
   1897, Landau 1899; equivalent to the prime number theorem), which is `mu_pnt_alt` of the
   PrimeNumberTheoremAnd project, vendored in `lib/PNTPlus`.
So both conjectures in the entry are true. The entry's own argument is incomplete (its bound
Sum_{j=N/2..N} 1/phi(j)^s, which also needs the pairing to be exact, does not apply at s = 1, where
the tail Sum_{N/2<j<=N} 1/phi(j) does not tend to 0).

**Argument.**
1. f(n) = mu(n)/phi(n)^z is multiplicative and |f| is summable for Re z > 1: the nonnegative
   multiplicative |f| has prime-power sums 1 + 1/(p−1)^σ, and Sum_p 1/(p−1)^σ < ∞, so its partial
   sums are bounded by the Euler product over smooth numbers. The Euler product
   Sum f = Prod_p (1 + f(p)) then holds, and its factor at p = 2 is 1 − 1/1^z = 0.
2. Write mu/phi = k * g (Dirichlet convolution) with g(m) = mu(m)/m and k = (mu/phi) * (1/id)
   (since (1/id) * (mu/id) = δ). k is multiplicative with k(p^e) = −1/((p−1)p^e) for e ≥ 1, so
   Sum |k(d)| = Prod_p (1 + 1/(p−1)^2) < ∞. Then
   Sum_{n<=N} mu(n)/phi(n) = Sum_{d<=N} k(d)·A(N/d), A(M) = Sum_{m<=M} mu(m)/m.
   A(M) → 0 and A is bounded, so each term tends to 0 and is dominated by B|k(d)|; Tannery's
   theorem gives the limit 0.

**Evidence.**
- Lean + Mathlib: [`A097945_mathlib.lean`](A097945_mathlib.lean). Main theorems
  `A097945.A097945_re_gt_one` (part 1, `HasSum (fun n => mu n / (phi n : ℂ)^z) 0` for 1 < Re z)
  and `A097945.A097945_conditional` (part 2: given `Tendsto (Sum_{m∈Ioc 0 N} mu m / m) atTop (𝓝 0)`,
  the partial sums of mu(n)/phi(n) and of a(n)/phi(n)^2, with `a n = mu n * phi n` as in the
  entry, tend to 0), and `A097945.A097945_s_one`, the same conclusion unconditionally, with the
  hypothesis supplied by `A097945.sum_mu_div_tendsto` (from `mu_pnt_alt`, lib/PNTPlus,
  PrimeNumberTheoremAnd rev 127b50e3). Helper `summable_of_mult` (summability of a nonnegative
  multiplicative function from its prime-power sums). Axioms of every theorem, including the
  vendored PNT: propext, Classical.choice, Quot.sound. Checked with tools/leancheck-mathlib.sh
  after tools/buildlib.sh, no warnings.
- `certificate/partial_sums.py` / `partial_sums.out`: S(10^k) for k ≤ 6
  (S(10^6) ≈ 3.1e-4).
- Outside Lean: that the Lean statements match the entry's text (reading).

**Review level.** `lean-proof` for both parts (part 2 through the vendored PNT, 2026-11-07).

**Prior art.** Searched 2026-11-06: current OEIS entry and history; web search for the series
Sum mu(n)/phi(n); arXiv (Gadiyar–Padma-type Ramanujan expansions use mu(q)/phi(q) as
coefficients but do not state this sum); google-deepmind/formal-conjectures (HEAD 2026-11-05)
and otoi-lab/oeis-lean-proofs (HEAD 2026-10-13), no entry. No source stating Sum mu(n)/phi(n) = 0
was found, but the deduction from Sum mu(n)/n = 0 by convolution with an absolutely summable
k is the standard Axer–Landau argument, and part 1 is a one-line Euler product remark. Verdict:
partly known (method classical, statement not found in print).
