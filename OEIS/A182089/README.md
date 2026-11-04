# OEIS A182089: (330k+7)(660k+13)(990k+19)(1980k+37) is Carmichael whenever its factors are prime

**Source.** OEIS [A182089](https://oeis.org/A182089), conjecture by Marius Coman (2012): "C = (330k+7)*(660k+13)*(990k+19)*(1980k+37) is a Carmichael number if 330k+7, 660k+13, 990k+19 and 1980k+37 are all four prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range k ≥ 0).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 36(55k+1)(215622000k^3+13068000k^2+263945k+1777) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

**Evidence.**
- Lean (Mathlib): [`A182089_mathlib.lean`](A182089_mathlib.lean) proves the full result (`A182089_main`): for every k, if 330k+7, 660k+13, 990k+19, 1980k+37 are prime then the product is Carmichael (`Nat.IsCarmichael`); Korselt via Mathlib, identities by `ring`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182089.lean`](A182089.lean): the identities N - 1 = (f - 1) Q
  for every factor, for all integers k (core Lean, `grind` ring normalisation). Outside Lean:
  Korselt's criterion (sufficiency), which needs Fermat's little theorem.
- `certificate/korselt_poly.py`: sympy division with zero remainder and integer quotients for all
  six families of this kind (A182085, A182088, A182089, A182132, A182133, A182416).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182089_mathlib.lean`](A182089_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182089.lean`](A182089.lean) checks the parts named under Evidence.

**Prior art.** Verdict known, immediate (OEIS status resolved-in-entry; searched 2026-11-04). Resolved in the entry; it is also Chernick's U_4 with m = 55k+1. Sources: [OEIS A182089 (fetched 2026-11-04)](https://oeis.org/A182089): 'The conjecture is true, and can be proved using Korselt's criterion' (A. Eldar, Apr 2024); [J. Chernick (1939), universal form U_4(m) = (6m+1)(12m+1)(18m+1)(36m+1); see OEIS A182518](https://oeis.org/A182518): Carmichael whenever all four factors are prime, any m. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history.
