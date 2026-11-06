# OEIS A207969, A207970: exp(Σ 5 F(n)^(2k) x^n/n) is an integer series

**Source.** [A207969](https://oeis.org/A207969) and [A207970](https://oeis.org/A207970) (P. D. Hanna,
Feb 22 2012), g.f. exp(Σ_{n≥1} 5 F(n)^4 x^n/n) and exp(Σ_{n≥1} 5 F(n)^6 x^n/n). Both entries state:
"Conjecture: exp( Sum_{n>=1} 5*Fibonacci(n)^(2*k) * x^n/n ) is an integer series for integers k>=0."
(OEIS text, CC BY-SA 4.0, revisions #16 and #23 of Oct 18 2020, checked 2026-11-06.)

**Result.** True for every k ≥ 0. (k = 2 and k = 3 are A207969 and A207970.)

**Argument.** For integers b(n), exp(Σ b(n) x^n/n) ∈ ℤ[[x]] as soon as b(m p^a) ≡ b(m p^(a-1)) (mod p^a)
for all primes p, a ≥ 1, m ≥ 1 (Gauss congruences): then b(n) = Σ_{d|n} d c(d) with integers c(d)
(Dwork), and the series is Π_d (1 - x^d)^(-c(d)). So it suffices to check the congruences for
b(n) = 5 F(n)^(2k). For k = 0, b = 5 is constant. Let k ≥ 1.

- *p ≠ 5.* With L(n) the Lucas numbers, 5 F(n)^2 = L(2n) - 2(-1)^n. Both n ↦ L(2n) and n ↦ (-1)^n
  satisfy the congruences: in ℤ[φ], z^p ≡ τ(z) (mod p) for a fixed τ ∈ {identity, conjugation}
  (from (2φ - 1)^2 = 5 and 5^((p-1)/2) ≡ ±1, or φ^2 ≡ conj(φ) mod 2), hence
  (φ^m)^(p^a) ≡ τ(φ^(m p^(a-1))) (mod p^a), and taking traces gives L(m p^a) ≡ L(m p^(a-1)).
  The congruences are preserved by sums and products, so (5F(n)^2)^k = 5^(k-1) b(n) satisfies them,
  and since 5 is a unit mod p, so does b.
- *p = 5.* 5^j | n implies 5^j | F(n) (from F(5m) = 5 F(m)(x^4 + 2x^3y + 4x^2y^2 + 3xy^3 + y^4) with
  x = F(m-1), y = F(m)). So 5^(a-1) | F(m 5^(a-1)) and 5^a | 5^(1+2k(a-1)) | b(m 5^(a-1)); the same
  holds for b(m 5^a). Hence both terms are 0 mod 5^a.

**Evidence.**
- Lean (Mathlib): [`A207969_mathlib.lean`](A207969_mathlib.lean). Main theorem
  `A207969_conjecture k n : ∃ z : ℤ, expCoeff (bseq k) n = z` with `bseq k n = 5 F(n)^(2k)` and
  `expCoeff b` the coefficients of exp(Σ b(n) x^n/n) given by A(0) = 1 and
  (n+1) A(n+1) = Σ_{j≤n} b(j+1) A(n-j). Steps: `frob`, `lucas_gauss`, `five_fib_sq`, `LG_bseq`
  (congruences), `dwork` (Euler exponents c(d)), `expCoeff_int_of_euler` (truncated Euler product in
  ℤ⟦X⟧ with the same log-derivative). Axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: exact rational recurrence; integral for k ≤ 6, n ≤ 80; matches the
  A207969 and A207970 data terms.
- Outside Lean: only the reading of "exp(...)" as the series fixed by A(0) = 1 and x A' = (Σ b x^n) A.

**Review level.** lean-proof.

**Prior art.** Checked 2026-11-06. Both entries still state the conjecture (P. Bala's algebraic
formulas for k = 2, 3 do not give integrality). The tools are standard (Gauss/Dold congruences,
Dwork's integrality lemma, closure of such sequences under products, the congruences for Lucas
numbers); no statement of this family's integrality was found (citations for the tools not
checked here). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs. Web search: OEIS pages only.
