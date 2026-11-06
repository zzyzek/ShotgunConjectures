# OEIS A030210: coefficients of (η(q)η(q^5))^4 satisfy |a(p)| < 2p^(3/2)

**Source.** OEIS [A030210](https://oeis.org/A030210) (offset 1): expansion of (eta(q) * eta(q^5))^4 in powers
of q. Conjecture (M. Somos, Oct 31 2005): "|a(p)| < 2*p^(3/2) for p prime." (OEIS text, CC BY-SA 4.0;
revision #45.)

**Result.** True for every prime p.

**Argument.** f(τ) = η(τ)^4 η(5τ)^4 is a cusp form of weight 4 on Γ_0(5) with trivial character (an
eta-quotient with Σ δr_δ = 24, Σ (5/δ)r_δ = 24, character from 5^4, a square; per the entry it is no. 13 in Martin's list of
multiplicative eta-quotients, Trans. AMS 348 (1996), Table I). S_4(Γ_0(5)) is 1-dimensional and has no old
forms (S_4(SL_2(ℤ)) = 0), so f is the normalised newform LMFDB
[5.4.a.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/5/4/a/a/) (q-expansion 1, −4, 2, 8, −5, −8, 6, 0,
−23, ..., eta-quotient η(z)^4η(5z)^4, Atkin–Lehner sign +1 at 5, not CM).

- p ≠ 5. P. Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974), Théorème 8.2: for a primitive
  (new) holomorphic cusp form on Γ_0(N) of weight k ≥ 2 with character, and p ∤ N, |a_p| ≤ 2p^{(k−1)/2}. With
  N = 5, k = 4: |a(p)| ≤ 2p^{3/2}. Equality would give a(p)^2 = 4p^3, impossible for an integer since p^3 is
  not a square. So |a(p)| < 2p^{3/2}.
- p = 5. For a newform with trivial character and p ∥ N, a_p = −w_p p^{k/2−1} with w_p the Atkin–Lehner
  eigenvalue (Atkin–Lehner 1970; standard, not re-read here). Here w_5 = +1, so a(5) = −5, matching the printed term and
  the entry's formula a(5^e) = (−5)^e. |a(5)| = 5 < 2·5^{3/2} ≈ 22.36.

**Evidence.**
- `certificate/check.py` (under a second): computes the product to q^10000 from Euler's pentagonal series;
  matches the 21 printed terms and LMFDB a(1..13); a(p)^2 < 4p^3 for all 1229 primes p < 10^4 (largest ratio
  |a(p)|/(2p^{3/2}) = 0.990, at p = 5591, a(p) = 827972); a(5) = −5.
- No Lean file (needs modular forms and Deligne's theorem).
- Outside Lean: Deligne's Ramanujan–Petersson bound (Weil I, Thm 8.2) and the identification of the
  eta-quotient with the newform 5.4.a.a.

**Review level.** `rechecked`. Théorème 8.2 read in the Numdam scan of Weil I; the LMFDB page read for the
q-expansion, eta-quotient and Atkin–Lehner sign; the identification re-derived from dim S_4(Γ_0(5)) = 1.

**Prior art.** Checked 2026-11-05: the entry does not cite Deligne (it links the LMFDB space of level 5,
weight 4 and Martin 1996) and still states the bound as a conjecture. Not in google-deepmind/formal-conjectures
(no `FormalConjectures/OEIS/30210.lean`).
