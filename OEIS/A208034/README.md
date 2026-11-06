# OEIS A208034: exp(Σ 2 Pell(n)^(2k) xⁿ/n) is an integer series; the odd-power and halved versions are not

**Source.** [A208034](https://oeis.org/A208034) (P. D. Hanna, Feb 2012), g.f.
exp(Σ_{n≥1} 2 Pell(n)² xⁿ/n), Pell = A000129. "Conjectures: For all positive integers k,
(1) exp( Sum_{n>=1} 2*Pell(n)^(2*k) * x^n/n ) is an integer series; (2) ... 2*Pell(n)^(2*k-1)
... is NOT an integer series; (3) ... Pell(n)^(2*k) ... is NOT an integer series."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** All three hold for every k ≥ 1 ((1) also for k = 0).

**Argument.** For integers b(n), exp(Σ b(n) xⁿ/n) ∈ ℤ[[x]] once b(m p^a) ≡ b(m p^(a−1))
(mod p^a) for all primes p, a, m ≥ 1 (Gauss congruences; then b(n) = Σ_{d|n} d c(d) with integer
c(d) and the series is Π_d (1 − x^d)^(−c(d))). For b(n) = 2 Pell(n)^(2k):
- *p odd.* In ℤ[√2], with α = 1 + √2, α^n = H(n) + Pell(n)√2 and Q(n) = tr α^n = 2H(n). Since
  2^((p−1)/2) ≡ ±1, z^p ≡ τ(z) (mod p) with τ the identity or conjugation, so Q(m p^a) ≡
  Q(m p^(a−1)) (mod p^a). Then 8 Pell(n)² = Q(2n) − 2(−1)ⁿ (norm of α^n is (−1)ⁿ); the
  congruences pass to products and differences, so 2(8 Pell(n)²)^k = 8^k b(n) satisfies them,
  and 8^k is a unit mod p.
- *p = 2.* Pell(2m) = 2 Pell(m) H(m), so 2^j | n gives 2^j | Pell(n); both b(m 2^a) and
  b(m 2^(a−1)) are divisible by 2^(1+2k(a−1)), a multiple of 2^a.

(2): with b(n) = 2 Pell(n)^m, m = 2k − 1 odd, the x³ coefficient is (4 + 6·2^m + 2·5^m)/3 and
4 + 2·5^m ≡ 4 − 2 = 2 (mod 3). (3): the x² coefficient of exp(Σ Pell(n)^(2k) xⁿ/n) is
(1 + 4^k)/2, not an integer.

**Evidence.**
- Lean (Mathlib): [`A208034_mathlib.lean`](A208034_mathlib.lean). `A208034_conj1 k n`:
  `∃ z : ℤ, expCoeff (bseq k) n = z` with `bseq k n = 2 * pell n ^ (2k)` (`A208034_int`: the
  entry, k = 1); `A208034_conj2`, `A208034_conj3` (k ≥ 1, non-integral coefficient of x³ resp.
  x²). `pell` is the A000129 recurrence; `expCoeff b` is the series fixed by A(0) = 1,
  (n+1)A(n+1) = Σ_{j≤n} b(j+1)A(n−j). The power-series part and the Dwork lemma are copied
  from [`../A207969/A207969_mathlib.lean`](../A207969/A207969_mathlib.lean) (Fibonacci analogue).
  Axioms propext, Classical.choice, Quot.sound; zero warnings.
- `certificate/check.py`: exact rationals; matches the entry's data; (1) integral for k ≤ 6,
  n ≤ 60; (2), (3) non-integral for k ≤ 6.
- Outside Lean: only the reading of "exp(...)" as the series fixed by A(0) = 1 and
  x A' = (Σ b(n) xⁿ) A.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry still states the conjectures. The tools are
standard (Gauss/Dold congruences, Dwork's integrality lemma); no proof of this family found by
web search. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
