# OEIS A182416: (60k+13)(180k+37)(300k+61) is Carmichael whenever its factors are prime

**Source.** OEIS [A182416](https://oeis.org/A182416), conjecture by Marius Coman (2012): "N = (60k+13)*(180k+37)*(300k+61) is a Carmichael number if (but not only if) 60k+13, 180k+37 and 300k+61 are all three prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range k ≥ 0).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 180(5k+1)(3600k^2+1532k+163) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

**Evidence.**
- Lean (Mathlib): [`A182416_mathlib.lean`](A182416_mathlib.lean) proves the full result (`A182416_main`): for every k, if 60k+13, 180k+37, 300k+61 are prime then the product is Carmichael (`Nat.IsCarmichael`); Korselt via Mathlib, identities by `ring`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182416.lean`](A182416.lean): the identities N - 1 = (f - 1) Q
  for every factor, for all integers k (core Lean, `grind` ring normalisation). Outside Lean:
  Korselt's criterion (sufficiency), which needs Fermat's little theorem.
- `certificate/korselt_poly.py`: sympy division with zero remainder and integer quotients for all
  six families of this kind (A182085, A182088, A182089, A182132, A182133, A182416).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182416_mathlib.lean`](A182416_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182416.lean`](A182416.lean) checks the parts named under Evidence.

**Prior art.** Known. The entry itself already resolves it: Greathouse comment (Oct 2012): the conjecture follows from Korselt's criterion (Chernick-type family) ([OEIS A182416](https://oeis.org/A182416), fetched 2026-11-04). Searched: entry, OEIS cross-reference search, edit history. Nothing new for OEIS. (Prior-art review 2026-11-04.)
