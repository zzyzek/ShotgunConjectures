# OEIS A138312 and A138313: kappa = B_3 - gamma

**Source.** [A138312](https://oeis.org/A138312) (decimal expansion of Mertens's constant B_3 minus Euler's constant,
B_3 - gamma = sum_p log p/(p(p-1)) = 0.7553666108...) and [A138313](https://oeis.org/A138313) (kappa =
lim (F_n - H_n), F_n = sum_{k<=n} mu^2(k)/phi(k), H_n the harmonic numbers). Each entry carries the comment that the
two constants are "conjectured to be equivalent" (OEIS text, CC BY-SA 4.0; A138312 as of Jul 28 2026, A138313 as of
Mar 07 2022; checked 2026-11-07). One grouped problem; A138313/README.md points here.

**Result.** True (known): kappa = sum_p log p/(p(p-1)) = B_3 - gamma.

**Argument.** Ramaré, Lemma 3.4 of the 1995 paper below (quoted as (12.12)-(12.14) in Helfgott's ternary Goldbach
book): for R >= 1, sum_{q<=R} mu^2(q)/phi(q) = log R + c_E + O*(7.284 R^(-1/3)) with
c_E = gamma + sum_p log p/(p(p-1)) = 1.3325822... Since H_n = log n + gamma + o(1), F_n - H_n -> c_E - gamma.
(The asymptotic log R + c_E goes back to Ward, J. London Math. Soc. 2 (1927); not read here.) Sketch of the
classical proof: n mu^2(n)/phi(n) = sum_{d|n} h(d) with h multiplicative, h(p) = 1/(p-1), h(p^2) = -p/(p-1),
h(p^k) = 0 for k >= 3; then sum_{n<=x} mu^2(n)/phi(n) = sum_d h(d)/d (log(x/d) + gamma + O(d/x)), and
sum_d h(d)/d = 1, -sum_d h(d) log d / d = sum_p log p/(p(p-1)) by logarithmic differentiation of the Euler product.

**Evidence.**
- `certificate/check.py`: F(10^6) - H(10^6) = 0.755358 against 0.7553666 (numerical illustration only).
- Lean: none (needs Mathlib analysis: Euler-product differentiation, harmonic-number asymptotics). Outside Lean: the
  whole identity, cited from Ramaré 1995.

**Review level.** `rechecked` (citation read in Helfgott's text; numerics agree).

**Prior art.** O. Ramaré, On Šnirel'man's constant, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 22 (1995) 645-706,
Lemma 3.4; H. A. Helfgott, The ternary Goldbach problem, arXiv:1501.05438, eqs. (12.12)-(12.14) and Lemma with
c_E = gamma + sum_p log p/(p(p-1)) (read 2026-11-07). Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
