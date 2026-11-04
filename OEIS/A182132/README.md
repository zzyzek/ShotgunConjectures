# OEIS A182132: (30n-7)(90n-23)(300n-79) is Carmichael whenever its factors are prime

**Source.** OEIS [A182132](https://oeis.org/A182132), conjecture by Marius Coman (2012): "The number C = (30n-7)*(90n-23)*(300n-79) is a Carmichael number if (but not only if) 30n-7, 90n-23 and 300n-79 are all three prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range n ≥ 1).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 60(4n-1)(15n-4)(225n-53) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

**Evidence.**
- Lean (Mathlib): [`A182132_mathlib.lean`](A182132_mathlib.lean) proves the full result (`A182132_main`): for every n, if 30n-7, 90n-23, 300n-79 are prime then the product is Carmichael (`Nat.IsCarmichael`); Korselt via Mathlib, identities by `ring`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182132.lean`](A182132.lean): the identities N - 1 = (f - 1) Q
  for every factor, for all integers k (core Lean, `grind` ring normalisation). Outside Lean:
  Korselt's criterion (sufficiency), which needs Fermat's little theorem.
- `certificate/korselt_poly.py`: sympy division with zero remainder and integer quotients for all
  six families of this kind (A182085, A182088, A182089, A182132, A182133, A182416).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182132_mathlib.lean`](A182132_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182132.lean`](A182132.lean) checks the parts named under Evidence.

**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). Standard Korselt/Chernick check for (m+1)(3m+1)(10m+1), m = 30n-8; not stated for this entry, unlike its sisters. Sources: [OEIS A182132 (fetched 2026-11-04)](https://oeis.org/A182132): still says Conjecture; Greathouse 2017 notes only the 7 | factors case for n = 5 mod 7; [OEIS A391076 (fetched 2026-11-04)](https://oeis.org/A391076): Korselt-identity remark for a different (five-factor) form; cross-references A182132. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A182416, A391076, A182518; Google: Chernick universal forms.
