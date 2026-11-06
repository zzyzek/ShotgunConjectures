# OEIS A183241, A182963, A174470, A165940, A157675, A156908, A156907: seven Hanna series are integer series

**Source.** Seven entries by P. D. Hanna (2009-2011), each with the comment "Conjectured to consist
entirely of integers." (OEIS text, CC BY-SA 4.0; entries read 2026-11-06: A183241 rev #12 and A182963 rev #8
of Sep 10 2026, the others rev #2 of Mar 30 2012). The seven claims share only this wording; each series
is different.

| id | series |
|---|---|
| A183241 | exp(Σ b(n) x^n/n), b = A183240(n) = Σ_{λ ⊢ n} (n!/Π λ_i!)^2 |
| A182963 | the same with cubes, b = A183235(n) |
| A174470 | exp(Σ t(n) (3x)^n/n), t = A014578 (t(n) = 1 if v_3(n) even, else 0) |
| A165940 | a(n) = 2^(n^2+n) [x^n] exp(Σ x^m/(m 2^(m^2))) |
| A157675 | A(x) = exp(Σ_{n≥1} A(2^n x)^n x^n/n) |
| A156907 | A(x) = 1 + x exp(Σ_{k≥1} (A(2^k x) - 1)^k/k) |
| A156908 | the same with 3^k |

**Result.** All seven are integer series (every coefficient is an integer).

**Argument.** Tool: if b(n) ∈ ℤ satisfies the Gauss congruences b(m p^a) ≡ b(m p^(a-1)) (mod p^a) for all
primes p, then b(n) = Σ_{d|n} d c(d) with c(d) ∈ ℤ and exp(Σ b(n) x^n/n) = Π_d (1 - x^d)^(-c(d)) ∈ ℤ[[x]]
(Dwork). Locally: if b(n) ∈ ℤ_(p) satisfies them at one prime p, the series lies in ℤ_(p)[[x]]
(Dieudonné-Dwork).

1. *A183241, A182963 (any power r ≥ 1).* Let X_n be the set of r-tuples of words of length n over
   {1, 2, ...} that all have the same content (c_1, ..., c_k) with c_1 ≥ ... ≥ c_k > 0 (letter i used c_i
   times, letters 1..k all used). Then |X_n| = Σ_{λ ⊢ n} (n!/Π λ_i!)^r = b(n). Rotating all r words at once is
   an action of ℤ/n on X_n. An element fixed by rotation by d (d | n) is the (n/d)-fold repetition of an
   element of X_d (content scales by n/d, preserving the conditions), and conversely. So the elements of
   exact period d form orbits of size d, and b(n) = Σ_{d|n} d c(d) with c(d) ≥ 0 the number of primitive
   orbits. Gauss congruences follow.
2. *A174470.* b(n) = t(n) 3^n. For p ≠ 3: t(m p^a) = t(m p^(a-1)) and 3^(m p^a) ≡ 3^(m p^(a-1)) (mod p^a)
   (Euler). For p = 3: m 3^(a-1) ≥ a, so 3^a divides both terms.
3. *A165940.* Put u(m) = 2^(-m^2). For odd p, 2 is a p-adic unit and 2^(-(m p^a)^2) / 2^(-(m p^(a-1))^2) =
   2^(-m^2 p^(2a-2) (p^2-1)) ≡ 1 (mod p^a), since p^(a-1)(p-1) divides the exponent; so
   [x^n] exp(Σ u(m) x^m/m) ∈ ℤ_(p). For p = 2: the coefficient is Σ_{λ ⊢ n} 2^(-Σ λ_i^2)/z_λ with
   z_λ | n!, and 2^(n^2+n) 2^(-Σ λ_i^2)/z_λ has 2-adic valuation ≥ n - v_2(n!) ≥ 1.
4. *A157675, A156907, A156908 (one lemma).* Lemma: let G(x, y) ∈ 1 + ℤ[[x, y]] with G(x, 0) = 1 and only
   monomials x^n y^k with n ≥ k (n ≥ 1), and let Φ be the ℚ-linear map x^n y^k ↦ q^(c(n,k)) x^n with
   c(jn, jk) = j^2 c(n, k) ≥ 0 and q ≥ 2 an integer. Then exp(Φ(log G)) ∈ ℤ[[x]]. Proof: G = Π_v (1 - x^v)^(e_v)
   over primitive-or-not v = (n, k) with e_v ∈ ℤ (graded induction), so log G = -Σ_v e_v Σ_j x^(jv)/j and
   exp(Φ log G) = Π_v E_v^(-e_v) with E_v = exp(Σ_j q^(j^2 c_v) x^(j n_v)/j). Each E_v is integral: β(j) =
   q^(j^2 c) satisfies Gauss congruences (p ∤ q: φ(p^a) | c m^2 p^(2a-2)(p^2-1); p | q and c ≥ 1: both terms
   divisible by p^(p^(2a-2)) and p^(2a-2) ≥ a; c = 0: β constant). The product converges x-adically.
   - A156907/A156908: with B = A - 1 ∈ xℤ[[x]], Σ_k (A(q^k x) - 1)^k/k = Φ(log 1/(1 - yB(x))) with
     Φ: x^n y^k ↦ q^(nk) x^n.
   - A157675: Σ_n A(2^n x)^n x^n/n = Φ(log 1/(1 - y x A(x))) with Φ: x^m y^n ↦ 2^(n(m-n)) x^m (m ≥ n).
   In each case [x^N] of the right side depends only on [x^(<N)] of A, so induction on N (A integral up to
   degree N-1 ⇒ G integral up to that degree ⇒ the lemma applied to the truncation gives A integral up to
   degree N) proves integrality.

**Evidence.**
- Lean (Mathlib), A174470 only: [`A174470_mathlib.lean`](A174470_mathlib.lean), namespace `A174470`, main
  theorem `A174470_int n : ∃ z : ℤ, expCoeff b n = z` with `b n = thue n * 3^n` and `thue` the entry's PARI
  formula for A014578. Gauss congruence `LG_b`; `dwork` and `expCoeff_int_of_euler` copied from
  [`../A181316/A181316_mathlib.lean`](../A181316/A181316_mathlib.lean). Check `tools/leancheck-mathlib.sh`: OK,
  no warnings, axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/multinomial_check.py`](certificate/multinomial_check.py): r = 2, 3, n ≤ 40: Gauss
  congruences of b and integrality; terms match the data.
- [`certificate/functional_check.py`](certificate/functional_check.py): A157675, A156907, A156908 exact to
  x^14, integral, match the data.
- [`certificate/a165940_a174470_check.py`](certificate/a165940_a174470_check.py): n ≤ 60 integral, data match.
- Lean (Mathlib), item 4: [`A157675_mathlib.lean`](A157675_mathlib.lean) (`A157675.A157675_int`) and
  [`A156907_mathlib.lean`](A156907_mathlib.lean) (`A156907.A156907_int`, `A156907.A156908_int`, every integer q via
  `a_int`); sequences defined from the functional equations (coefficient recurrences, `G(c x)` as polynomial
  composition), proof via the library [`lib/OpenProblemsLib/DworkEuler.lean`](../../lib/OpenProblemsLib/DworkEuler.lean) (`rowB_gauss` with W = (2^n)^(m-n), resp. (q^k)^m, and
  `recSeq_int`). Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice,
  Quot.sound.
- Lean (Mathlib), item 1: [`A183241_mathlib.lean`](A183241_mathlib.lean): `A183241.A183241_int`,
  `A183241.A182963_int` (`expCoeff (partitionSum r) n ∈ ℤ`, r = 2, 3, with `partitionSum r n = Σ_{λ ⊢ n}
  (n!/Π λ_i!)^r` over `Nat.Partition n`). The Gauss congruences are proved without the necklace action, by
  `LGp_partitionSum` in [`lib/OpenProblemsLib/DworkMultinomial.lean`](../../lib/OpenProblemsLib/DworkMultinomial.lean):
  (x_0 + ... + x_K)^(pn) ≡ (x_0^p + ... + x_K^p)^n mod p^(1+v_p n), so multinomial(pλ) ≡ multinomial(λ) and the
  multinomial of a partition of pn with a part prime to p is ≡ 0. Check `tools/leancheck-mathlib.sh`: OK, no
  warnings, axioms propext, Classical.choice, Quot.sound.
- Outside Lean: item 3 completely (A165940: the p-local Dwork criterion and the 2-adic bound; the library is
  integral, not p-local); for A183241, A182963, A157675, A156907, A156908 only the reading of exp(...) as the
  recurrence and data agreement; for A174470 only the reading of exp(...) as its recurrence and PARI's cutoff
  ceil(log m/log 3) (terms beyond it vanish).

**Review level.** A183241, A182963, A174470, A157675, A156907, A156908 `lean-proof`; A165940 `rechecked` (argument
re-derived, numerics).

**Prior art.** Checked 2026-11-06: all seven entries still say "Conjectured"; web search found only the
OEIS pages; none of the A-numbers is in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs
(local clones). The tools (Dwork's lemma, Dieudonné-Dwork, necklace/Dold sequences, Euler-product
factorisation) are standard; these applications were not found in print.
