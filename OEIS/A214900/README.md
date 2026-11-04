# OEIS A214900: every n is a sum of three squares and a fourth power

**Source.** OEIS [A214900](https://oeis.org/A214900): number of ordered representations
n = x² + y² + z² + w⁴. Conjecture (Sun, 2012): "a(n) != 0, that is, all numbers are sums of three
squares and one fourth power." (OEIS text, CC BY-SA 4.0.)

**Result.** True (given Legendre's three-square theorem).

**Argument.** Legendre: m is a sum of three squares iff m is not 4^a(8b+7). If n is not of that
form, w = 0. Otherwise n = 4^a(8b+7):
- a = 0: n - 1 = 8b + 6 ≡ 2 (mod 4) is not excluded; w = 1.
- a = 1: n - 1 = 32b + 27 is odd and ≡ 3 (mod 8); w = 1.
- a ≥ 2: n = 16m with m < n; if m = x² + y² + z² + w⁴ then n = (4x)² + (4y)² + (4z)² + (2w)⁴.

**Evidence.**
- [`A214900.lean`](A214900.lean): `main`, for all n, with Legendre's theorem (direction "not
  excluded ⇒ three squares") as a hypothesis (core Lean). Outside Lean: Legendre's theorem.
- `certificate/a214900.py`: three-square representability equals "not 4^a(8b+7)" and every n is
  representable, both for n ≤ 10^5.

**Review level.** `lean-witness` (the reduction is a Lean proof conditional on Legendre).

**Depends on (Mathlib).** Legendre's three-square theorem.

**Prior art.** Known. The sister entry [OEIS A270969](https://oeis.org/A270969) (fetched 2026-11-04) states it as a theorem with essentially our induction proof (Z.-W. Sun; see also [J. Number Theory 162 (2016)](https://doi.org/10.1016/j.jnt.2015.10.014)). [A214900](https://oeis.org/A214900) still says Conjecture and has no cross-reference to A270969, so an OEIS comment pointing there is useful. Searched: entry, OEIS cross-reference search, edit history, web. (Prior-art review 2026-11-04.)
