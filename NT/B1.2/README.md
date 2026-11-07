# Guy UPINT B1: Martin's alternating-divisor (k-imperfect) numbers for k ≥ 4

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B1 (paraphrased): with f multiplicative
and f(p^e) = p^e - p^(e-1) + p^(e-2) - ... + (-1)^e, Martin asks whether n = k f(n) has solutions for k ≥ 4, whether
there are infinitely many for k = 2, 3, and whether any odd solution exists for k = 3.

**Reading.** These n are the k-imperfect numbers (Iannucci; OEIS A127724, A127725, A127726, A328860). f = id ⋆ λ,
the Dirichlet convolution of the identity with the Liouville function, since both sides are multiplicative and agree
on prime powers.

**Result.** First question answered (known) for k = 4 and k = 5. 4-imperfect numbers: OEIS A328860, the smallest
993803899780063855042560. 5-imperfect: A. Wechsler (math-fun / Seqfan, 11 Feb 2020) found the 208-digit
N = 2^91·3^29·5^20·7^12·11^9·13^4·17·19·23^7·29·31^3·37·41·43·47^2·53^3·61^3·73·89·97·103·127·181·241·271·277·281·367·
449·683·1013·1657·1861·2411·3221·4561·5987·7603·13421·30269·139921·178481·2796203·228511817 with N = 5 f(N).
Open: k ≥ 6, infinitude for k = 2, 3, odd 3-imperfect numbers (none below 10^49 per A127726).

**Argument.** f(N) = Π f(p^e) with f(p^e) = (p^(e+1) + (-1)^e)/(p + 1); the product equals N/5.

**Evidence.**
- Lean (Mathlib): [`B1_2_mathlib.lean`](B1_2_mathlib.lean), namespace `NT_B1_2`. Main theorem `five_imperfect`:
  (N : ℤ) = 5 · rho N with rho = id ⋆ λ (`ArithmeticFunction.liouville`); `rho_prime_pow` proves
  rho(p^e) = Σ_{i ≤ e} p^i (-1)^(e-i) (Martin's definition), `rho_mult` multiplicativity. Primes above 10^5 by Pratt
  certificates (`bigprimes`). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext,
  Classical.choice, Quot.sound.
- [`certificate/check.gp`](certificate/check.gp): factorization and N / f(N) = 5 in PARI/gp.
- Outside Lean: the k = 4 examples (OEIS A328860, not rechecked here) and the open parts.

**Review level.** `lean-proof` for the k = 5 example.

**Prior art.** Checked 2026-11-06: OEIS A127724 (cites Wechsler's Seqfan post, Feb 2020), A328860, A127726;
math-fun thread "Progress in k-imperfect numbers" (11 Feb 2020) with the number. Not in
google-deepmind/formal-conjectures (clone 2026-11-06).
